-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:23.084803+00:00
-- url     : https://prove2.me/theorems/2a59628d-770e-4ea0-8b2b-dfaa79fdfd11
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ord Mod eq length quot sup 1026a45f8ec3: P2 M Ground Theory Heights  Heights Numbers DVR ord Mod eq length quot sup 1026a45f8ec3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ord Mod eq length quot sup 1026a45f8ec3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ord Mod eq length quot sup 1026a45f8ec3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/OrdModEqLengthQuotSup.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/OrdModEqLengthQuotSup.lean#L16-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
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
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3 (p : PrimeSpectrum A) (x : A) :
    ordMod p x = length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ordMod_eq_length_quot_sup» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ordMod_eq_length_quot_sup_1026a45f8ec3
