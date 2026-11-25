-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:46.355706+00:00
-- url     : https://prove2.me/theorems/24e4ab5f-d216-46ad-9790-caf8cf5af0d4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle unit aedc5c616d81: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle unit aedc5c616d81
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle unit aedc5c616d81 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle unit aedc5c616d81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L119-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81 (P : Ideal (MRing ι O)) (u : Oˣ) : divCycle P (C (u : O)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«divCycle_unit» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81
