-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_add_dd1c77339ebc
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_add_dd1c77339ebc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:32.791533+00:00
-- url     : https://prove2.me/theorems/c9551353-4592-48c6-85fc-2ad75402af99
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length length loc add dd1c77339ebc: P2 M Ground Theory Heights  Heights log Card Length length loc add dd1c77339ebc
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length length loc add dd1c77339ebc construction uses the P2 M Ground Theory Heights  Heights log Card Length length loc add dd1c77339ebc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L35-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
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
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_add_dd1c77339ebc {N₀ N₁ N₂ : Type} [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₀] [Module R N₁] [Module R N₂] (f : N₀ →ₗ[R] N₁) (g : N₁ →ₗ[R] N₂)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (m : Ideal R) [m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₁) =
      Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₀) +
        Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N₂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«length_loc_add» := P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_add_dd1c77339ebc
