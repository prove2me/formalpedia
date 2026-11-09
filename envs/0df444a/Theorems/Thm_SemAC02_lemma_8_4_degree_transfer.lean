-- Prove2me | Theorems.Thm_SemAC02_lemma_8_4_degree_transfer
-- name    : SemAC02.lemma_8_4_degree_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:20.795984+00:00
-- url     : https://prove2.me/theorems/df47ef06-f809-4f9f-9fca-55bf04b16519
-- title:
--   Lemma 8.4 — degree transfer and relative pseudo-reductions
-- statement:
--   Let $g$ be a gadget as in §8.1 on $m$ variables, $v=nm$, $S=\{[\![A]\!]:A\in\mathrm{Lift}_g(F_n)\}$ and $U$ the multiplier space (45) of $g$ (for any cutoff $k$). Let $F_n$ be an unsatisfiable CNF, $0\ne f\in U$ and $\ell\ge0$.
--
--   1. If $f$ has a PC derivation from $fS$ entirely in $f\mathcal B_v^{\le\ell}$, then $F_n$ has a PC refutation of degree at most $\ell+1$.
--   2. Consequently, if every PC refutation of $F_n$ has degree at least $\Delta_n$ and $\ell+1<\Delta_n$, the naïve relative pseudo-reduction $R_{f,\ell}$ for $S$ is non-zero.
--
--   Taking $\ell=3q$ supplies the operators that Theorem 4.16 requires.
--
--   Differences from the source:
--   - generalization: the base CNF of §8.1 (clauses with 1 ≤ |I| ≤ w₀) → any unsatisfiable CNF F; reason: if F has an empty clause, its clause polynomial 1 is a degree-0 refutation, so the first conclusion holds and the second is vacuous; the source's CNFs are a special case
--   - encoding: the gadget assumptions of §8.1 → 2 ≤ d and IsGadget d g; reason: the paper's circuits are in normal form by definition
--   - encoding: PC derivation and refutation in B_n; "a derivation of f" → PCNonBool.IsDerivation / PCNonBool.IsRefutation with reduction AC02Frege.ML; f (resp. 1) occurs as a line; reason: lines are the multilinear representatives; the extra axiom multiple 0·a only adds zero lines, which can be deleted without changing any other line or degree
--   - encoding: "every base refutation has degree at least Δ_n"; R_{f,ℓ} the quotient map (9) → PCDegreeAtLeast F Δ; naiveRelPR (quotient by the span of the derivable polynomials); reason: the derivable polynomials form a subspace (p.36), so the span adds nothing
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.4, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_IsGadget
import Definitions.Def_SemAC02_lift
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_SemAC02_PCDegreeAtLeast
import Definitions.Def_SemAC02_naiveRelPR
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_AC02Frege_ML

namespace SemAC02

/-- **Lemma 8.4 (Degree transfer and relative pseudo-reductions)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.4,
p.64): let `g` satisfy the assumptions of §8.1, `v = nm`, `S = {⟦A⟧ : A ∈ Lift_g(F_n)}` and `U` as
in (45). Let `F_n` be an unsatisfiable CNF, let `0 ≠ f ∈ U`, and let `ℓ ≥ 0` be an integer. If `f`
has a PC derivation from `fS` entirely in `f B_v^{≤ℓ}`, then `F_n` has a PC refutation of degree
at most `ℓ + 1`. Consequently, if every base refutation has degree at least `Δ_n` and
`ℓ + 1 < Δ_n`, the naïve relative pseudo-reduction `R_{f,ℓ}` for `S` is non-zero.

**Formalization Note** `U` is `multiplierSpace` of `g` for an arbitrary cutoff `k`. PC
refutations of `F_n` are the published `PCNonBool.IsRefutation` with reduction `AC02Frege.ML`
from the clause polynomials `⟦C⟧`, degree being total degree in `B_n`. "Every
base refutation has degree at least `Δ_n`" is `PCDegreeAtLeast F Δ`. `R_{f,ℓ}` is the quotient map
`naiveRelPR` (9). -/
theorem lemma_8_4_degree_transfer {d n m : ℕ} (hd : 2 ≤ d) (g : Circ (Fin m)) (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬ LiftSAParity.Satisfiable F) (k : ℕ)
    (f : MvPolynomial (Fin n × Fin m) (ZMod 2))
    (hfU : f ∈ multiplierSpace (fun X => g.eval X) n k) (hf : f ≠ 0) (ℓ : ℕ) :
    (RelDerivable (arith '' (lift g F : Set (Circ (Fin n × Fin m)))) f ℓ f →
      ∃ π : List (MvPolynomial (Fin n) (ZMod 2)),
        PCNonBool.IsRefutation AC02Frege.ML (pcAxioms F) π ∧ ∀ p ∈ π, p.totalDegree ≤ ℓ + 1) ∧
    (∀ Δ : ℕ, PCDegreeAtLeast F Δ → ℓ + 1 < Δ →
      naiveRelPR (arith '' (lift g F : Set (Circ (Fin n × Fin m)))) f ℓ ≠ 0) := by sorry

end SemAC02
