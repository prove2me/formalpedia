-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PluriTaylor_vec_expand__9b356877c8c0
-- name    : P2M_GlobalTheory_PluriTaylor_vec_expand__9b356877c8c0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:39.508345+00:00
-- url     : https://prove2.me/theorems/4be8a32a-9839-4c51-85db-abe0f5cc8943
-- title:
--   P2 M Global Theory Pluri Taylor vec expand  9b356877c8c0: P2 M Global Theory Pluri Taylor vec expand  9b356877c8c0
-- statement:
--   The P2 M Global Theory Pluri Taylor vec expand  9b356877c8c0 construction uses the P2 M Global Theory Pluri Taylor vec expand  9b356877c8c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformTaylorBoundLeviPluriharmonicSplit.lean#L19-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Complex Set
variable {n : ℕ}

theorem P2M_GlobalTheory_PluriTaylor_vec_expand__9b356877c8c0 (w : V n) : w = ∑ j, w j • bas n j := by sorry

alias «GlobalTheory».«PluriTaylor».«vec_expand'» := P2M_GlobalTheory_PluriTaylor_vec_expand__9b356877c8c0
