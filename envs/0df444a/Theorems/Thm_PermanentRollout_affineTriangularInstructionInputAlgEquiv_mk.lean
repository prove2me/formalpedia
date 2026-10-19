-- Prove2me | Theorems.Thm_PermanentRollout_affineTriangularInstructionInputAlgEquiv_mk
-- name    : PermanentRollout.affineTriangularInstructionInputAlgEquiv_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/998ef928-b6cc-4fd5-a922-847bd0d994a3
-- title:
--   PermanentRollout.affineTriangularInstructionInputAlgEquiv_mk
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

theorem PermanentRollout.affineTriangularInstructionInputAlgEquiv_mk
    {k q : ℕ}
    (rhs : Fin q → MvPolynomial (Fin k ⊕ Fin q) ℂ)
    (gate : Fin q → MvPolynomial (Fin k) ℂ)
    (hgate : ∀ j, gate j = affineGateGraphEvaluation gate (rhs j))
    (htop : ∀ j i : Fin q,
      Sum.inr i ∈ (rhs j).vars → i.val < j.val)
    (p : MvPolynomial (Fin k ⊕ Fin q) ℂ) :
    affineTriangularInstructionInputAlgEquiv rhs gate hgate htop
      (Ideal.Quotient.mk (affineTriangularInstructionIdeal rhs) p) =
        affineGateGraphEvaluation gate p := by sorry
