-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_mono_696bf728cb33
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_mono_696bf728cb33
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:23.109831+00:00
-- url     : https://prove2.me/theorems/d6101497-79f4-554c-aa07-3fd0290b478a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull mono 696bf728cb33: P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull mono 696bf728cb33
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull mono 696bf728cb33 construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull mono 696bf728cb33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L27-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono

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
omit [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_mono_696bf728cb33 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixed».«PrefixPull».«mono» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_mono_696bf728cb33
