-- Prove2me | Theorems.Thm_PrettyGoodShadow_copy_accounting
-- name    : PrettyGoodShadow.copy_accounting
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:13.449956+00:00
-- url     : https://prove2.me/theorems/f2727e0e-22ff-43a2-86db-0b521bf65eaf
-- title:
--   Appendix A, p.32 — the boosted algorithm is one POVM on $R\cdot k(2T-1)$ copies
-- statement:
--   Let $k,T\ge1$ and $N=R\cdot k(2T-1)$. There is one POVM on $N$ copies, which does not depend on the input label, with outcomes $(t_r,y_r)_{r\in[R]}$, $t_r\in\{T,\dots,2T-1\}$, $y_r\in\mathcal L$, such that for every $x$ with $p_x>0$ the outcome has probability
--
--   $$
--   \prod_{r=1}^R\frac1T\Pr\big[\text{the PGM of }q_r\text{ on }kt_r\text{ copies of }\rho_x\text{ outputs }y_r\big].
--   $$
--
--   Summing over the $t_r$ gives the joint law used in the failure probability, so the guarantees of the algorithm are guarantees of a single measurement on $N$ copies.
--
--   **Formalization Note** The pretty good measurement operators sum to the projector on the support, so the POVM completes them off that support, as the source allows on p.16.
--
--   Differences from the source:
--   - encoding: the R estimators are applied independently to disjoint sets of copies; each uses at most k(2T − 1) copies → one explicit POVM on R·k(2T − 1) copies, with the sampled t_r among its outcomes, and its outcome law; reason: this is what independent runs on disjoint copies are, written as one measurement; unused copies are traced out
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Appendix A, p.32

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_PrettyGoodShadow_failureProb

namespace PrettyGoodShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Copy accounting** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.32). "Since the `R` estimators are applied
independently to disjoint sets of copies", the boosted algorithm is one POVM on `R · k(2T − 1)` copies: its outcomes are
the sampled copy numbers and the labels `(t_r, y_r)` of each round, it does not depend on the input label, and on
`ρ_x^{⊗N}` with `p_x > 0` the outcome `(t, y)` has probability `∏_r T⁻¹ · Pr[PGM of q_r on k t_r copies outputs y_r]`.

**Formalization Note** The PGM operators sum to the projector on `supp(S)`, so the POVM completes them off that support, as
the page allows (p.16); no `ρ_x^{⊗n}` with `p_x > 0` sees the completion. `2 * T - 1` is a natural subtraction with
`T ≥ 1`. -/
theorem copy_accounting {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] {m : ℕ}
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (p : L → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (O : Fin m → Matrix d d ℂ) (ε : ℝ) (k T R : ℕ)
    (hk : 1 ≤ k) (hT : 1 ≤ T) :
    ∃ N : (Fin R → ↥(Finset.Ico T (2 * T)) × L) →
        Matrix (Fin (R * (k * (2 * T - 1))) → d) (Fin (R * (k * (2 * T - 1))) → d) ℂ,
      QAlgorithms.IsPOVM N ∧
      ∀ (x : L), 0 < p x → ∀ z : Fin R → ↥(Finset.Ico T (2 * T)) × L,
        (N z * tensorPow (ρ x) (R * (k * (2 * T - 1)))).trace.re =
          ∏ r : Fin R, (T : ℝ)⁻¹ *
            pgmLaw (prior p ρ O ε k T r) ρ (k * ((z r).1 : ℕ)) x (z r).2 := by sorry

end PrettyGoodShadow
