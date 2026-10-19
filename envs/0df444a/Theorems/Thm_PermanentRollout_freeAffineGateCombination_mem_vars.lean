-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineGateCombination_mem_vars
-- name    : PermanentRollout.freeAffineGateCombination_mem_vars
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/df0a9094-3398-43a6-ad38-7e7c71c59a12
-- title:
--   PermanentRollout.freeAffineGateCombination_mem_vars
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.freeAffineGateCombination_mem_vars
    {k n : ℕ} (coefficients : ℕ →₀ ℂ) (i : Fin n)
    (hi : Sum.inr i ∈
      (Finsupp.linearCombination ℂ
        (freeAffineGateReference (k := k) (n := n))
        coefficients).vars) :
    ∃ r ∈ coefficients.support, i.val = r := by sorry
