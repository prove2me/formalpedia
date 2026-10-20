-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution
-- name    : PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/ec95c1af-ebc1-4096-acf5-66a7ce6f90bb
-- title:
--   PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators

theorem PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    (MvPolynomial.finSuccEquiv ℂ n
      (MvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) j) p)).eval
        (homogeneousMapFinSuccFirstPivotPlaneRoot
          (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))) =
      MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial
          (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row) p := by sorry
