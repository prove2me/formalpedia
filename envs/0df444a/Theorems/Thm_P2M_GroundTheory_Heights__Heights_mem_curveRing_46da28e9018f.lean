-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f
-- name    : P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:48.345715+00:00
-- url     : https://prove2.me/theorems/4ef0619d-2c0c-4d74-9ade-b1e37a64a89b
-- title:
--   P2 M Ground Theory Heights  Heights mem curve Ring 46da28e9018f: P2 M Ground Theory Heights  Heights mem curve Ring 46da28e9018f
-- statement:
--   The P2 M Ground Theory Heights  Heights mem curve Ring 46da28e9018f construction uses the P2 M Ground Theory Heights  Heights mem curve Ring 46da28e9018f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsPointVertRSteps.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsPointVertRSteps.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f {y : (Σ k, ι k) → Ω} {b : Ω} :
    b ∈ curveRing y ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ y c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_curveRing» := P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f
