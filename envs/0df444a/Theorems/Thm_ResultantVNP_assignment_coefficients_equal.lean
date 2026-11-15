-- Prove2me | Theorems.Thm_ResultantVNP_assignment_coefficients_equal
-- name    : ResultantVNP.assignment_coefficients_equal
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T13:10:58.831205+00:00
-- url     : https://prove2.me/theorems/202e3a1e-959f-4c8c-b8a8-772731ccf696
-- title:
--   Equality of assignment coefficients across grid class partitions
-- statement:
--   For a fixed resultant system, grid side m > 0, and total number n of tensor indices, any two grid assignments have the same coefficient in the degree m² characteristic coefficient polynomial. The two assignments may use different class maps. Thus the coefficient depends only on the resultant system, n, and m, not on the class partition or on the assignment. This statement establishes the equality part of Theorem 3.5; it makes no assertion that the common coefficient is nonzero.
-- source:
--   Equality part of Theorem 3.5 in Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103. Proof by extending the bijection between chosen indices to a permutation and applying characteristic-coefficient invariance.

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Definitions.Def_ResultantVNP_gridSum

theorem ResultantVNP.assignment_coefficients_equal (𝓡 : ResultantVNP.ResultantSystem) (m n : ℕ) [NeZero m]
    (cls cls' : Fin n → ZMod m × ZMod m)
    (ν : ∀ p,{a // cls a = p}) (η : ∀ p,{a // cls' a = p}) :
    (ResultantVNP.charCoeff 𝓡 n (m^2)).coeff (ResultantVNP.assignMonomial cls ν) =
      (ResultantVNP.charCoeff 𝓡 n (m^2)).coeff (ResultantVNP.assignMonomial cls' η) := by sorry
