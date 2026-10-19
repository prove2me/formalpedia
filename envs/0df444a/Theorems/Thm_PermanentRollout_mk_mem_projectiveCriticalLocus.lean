-- Prove2me | Theorems.Thm_PermanentRollout_mk_mem_projectiveCriticalLocus
-- name    : PermanentRollout.mk_mem_projectiveCriticalLocus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/9d8ae374-cde8-46f0-8d7c-03d09810ddcf
-- title:
--   PermanentRollout.mk_mem_projectiveCriticalLocus
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

theorem PermanentRollout.mk_mem_projectiveCriticalLocus {m : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ)
    (hv : v ≠ 0) (hcritical : v ∈ criticalLocus P) :
    Projectivization.mk ℂ v hv ∈ projectiveCriticalLocus P := by sorry
