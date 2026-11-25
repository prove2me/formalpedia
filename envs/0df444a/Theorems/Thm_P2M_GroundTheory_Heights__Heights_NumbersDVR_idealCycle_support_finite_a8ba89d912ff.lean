-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_support_finite_a8ba89d912ff
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_support_finite_a8ba89d912ff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:51.260004+00:00
-- url     : https://prove2.me/theorems/4ee2dc9d-ed63-4d5e-87f3-6002f01e7126
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle support finite a8ba89d912ff: P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle support finite a8ba89d912ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle support finite a8ba89d912ff construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ideal Cycle support finite a8ba89d912ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IdealCycleSupportFinite.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IdealCycleSupportFinite.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IdealCycleSupportFinite
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
open MvPolynomial
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_support_finite_a8ba89d912ff {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«idealCycle_support_finite» := P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_support_finite_a8ba89d912ff
