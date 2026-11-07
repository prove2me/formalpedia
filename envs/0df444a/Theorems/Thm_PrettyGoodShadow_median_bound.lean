-- Prove2me | Theorems.Thm_PrettyGoodShadow_median_bound
-- name    : PrettyGoodShadow.median_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:32:57.848036+00:00
-- url     : https://prove2.me/theorems/ec305772-e01a-45a7-be94-b94ffd41a8f5
-- title:
--   Appendix A, p.32 — the median misses with probability at most $3^{-R/2}\prod_r(1+2e_{q_r}(x))$, and at most $m(\sqrt3/2)^R$ overall
-- statement:
--   Let $R$ be odd and $k,T\ge1$. For every label $x$ and every observable $O_i$,
--
--   $$
--   \Pr\big[|\hat o_i-\operatorname{tr}(O_i\rho_x)|>\varepsilon\,\big|\,x\big]\le3^{-R/2}\prod_{r=1}^R\big(1+2e_{q_r}(x)\big),
--   $$
--
--   where $\hat o_i$ is the median of the $R$ independent estimators. If in addition $k\ge48/\varepsilon^2$ and $2me^{-T/128}\le1/8$, then averaging over $x\sim p$ gives at most $(\sqrt3/2)^R$ for each $i$, and the union bound gives
--
--   $$
--   \Pr\Big[\max_{i\in[m]}|\hat o_i-\operatorname{tr}(O_i\rho)|>\varepsilon\Big]\le m\Big(\frac{\sqrt3}{2}\Big)^R .
--   $$
--
--   This amplification step yields the factor $\log(m/\delta)$ in the copy complexity.
--
--   **Formalization Note** $3^{-R/2}$ is a real power.
--
--   Differences from the source:
--   - reading: k = ⌈12/ε²⌉ (p.18; "these parameters", p.31) with ∥O_i∥∞ ≤ 1 → k ≥ 48/ε²; reason: the bound at this point rests on Lemma 4.3 in the normalized form, whose threshold for ∥O∥∞ ≤ 1 is 48/ε²; k enters the theorem only through O(·)
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Appendix A, p.32

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_PrettyGoodShadow_failureProb

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow

/-- **The median bound** (arXiv:2610.06781, sha256 bd055b7d…, Appendix A, p.32). For odd `R`, a state `ρ_x` and an observable
`O_i`, the median of `R` independent estimators errs with probability at most `3^{−R/2} ∏_r (1 + 2 e_{q_r}(x))`.
Under the parameter conditions of the proof, averaging over `x ∼ p` gives at most `(√3/2)^R` for each `i`, and the union
bound over the `m` observables gives `Pr[max_i |ô_i − tr(O_i ρ)| > ε] ≤ m (√3/2)^R`.

**Formalization Note** The first clause holds for every label `x`, including `p_x = 0`, since its proof only needs each
`alg1Law` to have total mass at most `1`. `3^{−R/2}` is a real power. -/
theorem median_bound {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (p : L → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (m : ℕ) (hm : 1 ≤ m) (O : Fin m → Matrix d d ℂ)
    (hOh : ∀ i, (O i).IsHermitian) (hOn : ∀ i, ‖O i‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) (k T R : ℕ)
    (hk : 1 ≤ k) (hT : 1 ≤ T) (hR : Odd R) :
    (∀ (x : L) (i : Fin m),
      ∑ y : Fin R → L with ε < |medianOdd (fun r => obs (O i) (ρ (y r))) - obs (O i) (ρ x)|,
          ∏ r : Fin R, alg1Law (prior p ρ O ε k T r) ρ k T x (y r) ≤
        (3 : ℝ) ^ (-(R : ℝ) / 2) * ∏ r : Fin R, (1 + 2 * maxErr (prior p ρ O ε k T r) ρ O k T ε x)) ∧
    (48 / ε ^ 2 ≤ (k : ℝ) → 2 * (m : ℝ) * Real.exp (-(T : ℝ) / 128) ≤ 1 / 8 →
      (∀ i : Fin m, ∑ x, p x * ∑ y : Fin R → L with
            ε < |medianOdd (fun r => obs (O i) (ρ (y r))) - obs (O i) (ρ x)|,
          ∏ r : Fin R, alg1Law (prior p ρ O ε k T r) ρ k T x (y r) ≤ (Real.sqrt 3 / 2) ^ R) ∧
      failureProb p ρ O ε k T R ≤ (m : ℝ) * (Real.sqrt 3 / 2) ^ R) := by sorry

end PrettyGoodShadow
