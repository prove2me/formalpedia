-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
-- name    : PermanentRollout.homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/68580458-d008-467b-8099-9f519bcc26ce
-- title:
--   PermanentRollout.homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
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

theorem PermanentRollout.homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : ι → ℂ)
    (t : homogeneousMapSubalgebra F) :
    (t : MvPolynomial ι ℂ) -
        MvPolynomial.C
          (((MvPolynomial.aeval target).comp
            (homogeneousMapCoordinateAlgEquiv F e he hF hzero).symm.toAlgHom) t) ∈
      homogeneousMapFiberIdeal F target := by sorry
