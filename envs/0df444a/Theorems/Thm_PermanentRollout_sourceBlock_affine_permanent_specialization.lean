-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlock_affine_permanent_specialization
-- name    : PermanentRollout.sourceBlock_affine_permanent_specialization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/790cb5fd-a1ba-477b-a458-7b9b6f550e94
-- title:
--   PermanentRollout.sourceBlock_affine_permanent_specialization
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.sourceBlock_affine_permanent_specialization
    {n r s d : ℕ}
    (rowEquiv : Fin n ≃ Fin r ⊕ Fin (s - d))
    (columnEquiv : Fin n ≃ Fin s ⊕ Fin (r - d))
    (U : Matrix (Fin r) (Fin (r - d)) ℂ) :
    MvPolynomial.aeval
        (fun ij : Fin n × Fin n =>
          (sourceBlockAffineInput U
            (rowEquiv ij.1) (columnEquiv ij.2)).polynomial)
        (permanent n) =
      rectangularPermanent
        (sourceBlockMatrix r s d
          (fun i j =>
            MvPolynomial.X
              ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
                (i, j)))
          (fun i j =>
            algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ)
              (U i j))) := by sorry
