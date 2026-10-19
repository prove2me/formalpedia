-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockMatrix_rectangularPermanent_flatten
-- name    : PermanentRollout.sourceBlockMatrix_rectangularPermanent_flatten
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/0deda884-7210-420b-b4bb-62c18bb7a441
-- title:
--   PermanentRollout.sourceBlockMatrix_rectangularPermanent_flatten
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

theorem PermanentRollout.sourceBlockMatrix_rectangularPermanent_flatten
    (r s d : ℕ) (U : Matrix (Fin r) (Fin (r - d)) ℂ) :
    rectangularPermanent
        (sourceBlockMatrix r s d
          (fun i j =>
            (MvPolynomial.X
              ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
                (i, j)) : MvPolynomial (Fin (r * s)) ℂ))
          (fun i j =>
            algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ) (U i j))) =
      MvPolynomial.rename
        (finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
        (rectangularPermanent
          (sourceBlockMatrix r s d
            (fun i j =>
              (MvPolynomial.X (i, j) :
                MvPolynomial (Fin r × Fin s) ℂ))
            (fun i j =>
              algebraMap ℂ (MvPolynomial (Fin r × Fin s) ℂ)
                (U i j)))) := by sorry
