-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_support_finite_d90d2125fc12
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_support_finite_d90d2125fc12
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:28.224611+00:00
-- url     : https://prove2.me/theorems/e050d918-cea4-5dea-9923-9101f61f8979
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle support finite d90d2125fc12: P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle support finite d90d2125
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle support finite d90d2125fc12 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Scalar Quotient div Cycle support finite d90d2125fc12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PScalarQuotient.lean#L107-L115

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_support_finite_d90d2125fc12 (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ScalarQuotient».«divCycle_support_finite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_support_finite_d90d2125fc12
