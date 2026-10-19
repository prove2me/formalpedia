-- Prove2me | Theorems.Thm_PermanentRollout_zeroLocus_gradientIdeal_eq_criticalLocus
-- name    : PermanentRollout.zeroLocus_gradientIdeal_eq_criticalLocus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/4e947492-d1e5-4cde-9246-62a4595a569d
-- title:
--   PermanentRollout.zeroLocus_gradientIdeal_eq_criticalLocus
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

theorem PermanentRollout.zeroLocus_gradientIdeal_eq_criticalLocus {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.zeroLocus ℂ
        (homogeneousMapIdeal (fun i : Fin m => MvPolynomial.pderiv i P)) =
      criticalLocus P := by sorry
