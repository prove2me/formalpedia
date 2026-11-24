-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f
-- name    : P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:37.816801+00:00
-- url     : https://prove2.me/theorems/f6ddfcd1-1561-4906-894c-a7ab237d615f
-- title:
--   P2 M Ground Theory Heights  Heights continuous area Jacobian b8921d31322f: P2 M Ground Theory Heights  Heights continuous area Jacobian b8921d31322f
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous area Jacobian b8921d31322f construction uses the P2 M Ground Theory Heights  Heights continuous area Jacobian b8921d31322f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L35-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
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
open MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_areaJacobian» := P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f
