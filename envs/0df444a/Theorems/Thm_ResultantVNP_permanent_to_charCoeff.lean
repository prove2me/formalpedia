-- Prove2me | Theorems.Thm_ResultantVNP_permanent_to_charCoeff
-- name    : ResultantVNP.permanent_to_charCoeff
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T16:31:47.88414+00:00
-- url     : https://prove2.me/theorems/2decf192-bddc-4554-82eb-9cc0ec941082
-- title:
--   Rational p-projections from the permanent to tensor characteristic coefficients
-- statement:
--   For every resultant system, the generic permanent family is a p-projection of the characteristic-coefficient family Phi_{5m^2,m^2}, with m at least 3 and polynomially bounded in the permanent size. Every substituted constant is rational. This is the explicit reduction clause of Theorem 3.2, separate from the general VNP-completeness theorem for the permanent.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103, Theorem 3.2 and its proof on p.17.

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_PolyBounded

theorem ResultantVNP.permanent_to_charCoeff (𝓡 : ResultantVNP.ResultantSystem) :
    ∃ t : ℕ → ℕ, ResultantVNP.PolyBounded t ∧ ∀ n, 1 ≤ n → 3 ≤ t n ∧
      ∃ ρ : Sym (Fin (5 * t n ^ 2)) 3 → (Fin n × Fin n) ⊕ ℚ,
        MvPolynomial.aeval
          (fun T => Sum.elim MvPolynomial.X (fun q : ℚ => MvPolynomial.C (q : ℂ)) (ρ T))
          (MvPolynomial.map (Int.castRingHom ℂ)
            (ResultantVNP.charCoeff 𝓡 (5 * t n ^ 2) (t n ^ 2))) =
          (Matrix.of fun i j : Fin n =>
            (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent := by sorry
