-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b
-- name    : P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:08.683032+00:00
-- url     : https://prove2.me/theorems/01d6c136-7bd8-4740-b8ac-f632a7d778df
-- title:
--   P2 M Ground Theory Heights  Heights Proj Dim Spread has Projective Dimension LE zero iff bc36fa0f4b8b: P2 M Ground Theory Heights  Heights Proj Dim Spread has Projective Dimension LE zero iff bc36fa0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Dim Spread has Projective Dimension LE zero iff bc36fa0f4b8b construction uses the P2 M Ground Theory Heights  Heights Proj Dim Spread has Projective Dimension LE zero iff bc36fa0f4b8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
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
open CategoryTheory
variable {R : Type} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b (M : ModuleCat.{0} R) (S : Submonoid R) :
    HasProjectiveDimensionLE (M.localizedModule S) 0 ↔
      Module.Projective (Localization S) (LocalizedModule S M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjDimSpread».«hasProjectiveDimensionLE_zero_iff» := P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b
