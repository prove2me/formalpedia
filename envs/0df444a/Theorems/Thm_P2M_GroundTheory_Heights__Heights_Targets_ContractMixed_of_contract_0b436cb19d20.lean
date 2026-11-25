-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_of_contract_0b436cb19d20
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_of_contract_0b436cb19d20
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:44.151745+00:00
-- url     : https://prove2.me/theorems/947c30cb-4918-4402-9f3d-4430ff171a53
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed of contract 0b436cb19d20: P2 M Ground Theory Heights  Heights Targets Contract Mixed of contract 0b436cb19d20
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed of contract 0b436cb19d20 construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed of contract 0b436cb19d20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L137-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L137-L150

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_of_contract_0b436cb19d20 (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixed».«of_contract» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_of_contract_0b436cb19d20
