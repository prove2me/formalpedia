-- Prove2me | Theorems.Thm_PrettyGoodShadow_definition_3_1_validity
-- name    : PrettyGoodShadow.definition_3_1_validity
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:25:55.118443+00:00
-- url     : https://prove2.me/theorems/a9d9b47b-0104-4da9-9280-f9dafed0593f
-- title:
--   Definition 3.1 (validity) — $D_S$ is positive, $D_S(S)=\Pi$, and the integral PGM is a measurement
-- statement:
--   Let $S$ be positive semidefinite with support projector $\Pi$. Then the integrand defining $D_S(X)$ is integrable for every $X$, the map $D_S$ is positive, and
--
--   $$
--   D_S(S)=\Pi .
--   $$
--
--   Consequently, for a finite ensemble of states with prior $p$, the operators $M_y=D_S(p_y\rho_y^{\otimes n})$ are positive semidefinite with $\sum_y M_y=\Pi$, and for every label $x$ with $p_x>0$ the numbers $\operatorname{tr}(M_y\rho_x^{\otimes n})$ form a probability vector in $y$.
--
--   This is what makes the integral pretty good measurement a valid measurement on every state of the ensemble. The source states it and omits the details.
--
--   **Formalization Note** Integrability is part of the statement, so that the identity cannot come from the junk value of a non-integrable Bochner integral.
--
--   Differences from the source:
--   - generalization: S is the average state S(p, n) → S is any positive semidefinite operator; reason: the proof uses only that S is positive definite on its support, and S(p, n) is one such operator
--   - encoding: D_S(S) = I on supp(S) → divS S S = suppProj S on the whole space; reason: the identity on supp(S) extended by 0 is the projector Π; p.16 says "on supp(S)"
--   - encoding: the M_x form a POVM on supp(S), completed arbitrarily → the M_y sum to Π, and tr(M_y ρ_x^{⊗n}) is a probability vector for p_x > 0; reason: no state with p_x > 0 sees the completion; the completion itself is in copy_accounting
--   - encoding: D_S is an integral → integrability of the integrand is stated as a clause; reason: it rules out the Bochner junk value; it adds a conclusion and no hypothesis
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Definition 3.1, p.16

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_PrettyGoodShadow_pgmEffect

open MeasureTheory
open scoped ComplexOrder

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

/-- **Definition 3.1, validity claim** (arXiv:2610.06781, sha256 bd055b7d…, p.16). For a positive semidefinite
`S` the integrand of `D_S` is integrable, `D_S` is positive and `D_S(S) = Π`. Hence for a finite ensemble of
states the operators `M_y = D_S(p_y ρ_y^{⊗n})` are positive semidefinite and sum to `Π`, and on a state `ρ_x`
with `p_x > 0` they give a probability vector.

**Formalization Note** Integrability is part of the statement, so that `D_S(S) = Π` cannot come from the junk
value of a non-integrable Bochner integral. `D_S(S) = I` on the page means the identity on `supp(S)`, that is,
`Π` on the whole space (p.16). -/
theorem definition_3_1_validity :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℂ), S.PosSemidef →
      (∀ (X : Matrix ι ι ℂ) (a b : ι),
        IntegrableOn (fun t : ℝ => (shiftInv S t * X * shiftInv S t) a b) (Set.Ioi 0)) ∧
      (∀ X : Matrix ι ι ℂ, X.PosSemidef → (divS S X).PosSemidef) ∧
      divS S S = suppProj S) ∧
    (∀ {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ) (p : L → ℝ)
      (n : ℕ), (∀ x, WildeQIT.IsDensityOperator (ρ x)) → (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      (∀ y, (pgmEffect p ρ n y).PosSemidef) ∧
      ∑ y, pgmEffect p ρ n y = suppProj (ensembleState p ρ n) ∧
      (∀ x, 0 < p x → (∀ y, 0 ≤ pgmLaw p ρ n x y) ∧ ∑ y, pgmLaw p ρ n x y = 1)) := by sorry

end PrettyGoodShadow
