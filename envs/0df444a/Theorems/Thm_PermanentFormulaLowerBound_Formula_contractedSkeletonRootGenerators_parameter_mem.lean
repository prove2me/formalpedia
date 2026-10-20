-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_contractedSkeletonRootGenerators_parameter_mem
-- name    : PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_parameter_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/be6e39b6-1e36-4ebe-a6a6-9c810ac2bf6e
-- title:
--   PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_parameter_mem
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
variable [Field F]

theorem PermanentFormulaLowerBound.Formula.contractedSkeletonRootGenerators_parameter_mem
    {f : Formula (Y ⊕ Z) F}
    (w : ContractedSkeleton f)
    {a : FractionRing (MvPolynomial Z F)}
    (ha : a ∈ contractedSkeletonRootExtras w) :
    a ∈ IntermediateField.adjoin F
      (↑(contractedSkeletonRootGenerators w) :
        Set (FractionRing (MvPolynomial Z F))) := by sorry
