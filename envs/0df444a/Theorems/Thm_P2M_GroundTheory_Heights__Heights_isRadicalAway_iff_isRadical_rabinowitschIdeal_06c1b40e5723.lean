-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAway_iff_isRadical_rabinowitschIdeal_06c1b40e5723
-- name    : P2M_GroundTheory_Heights__Heights_isRadicalAway_iff_isRadical_rabinowitschIdeal_06c1b40e5723
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:18.880258+00:00
-- url     : https://prove2.me/theorems/18afa784-9024-468b-9242-319b76c499bb
-- title:
--   P2 M Ground Theory Heights  Heights is Radical Away iff is Radical rabinowitsch Ideal 06c1b40e5723: P2 M Ground Theory Heights  Heights is Radical Away iff is Radical rabinowitsch Ideal 06c1b40e5723
-- statement:
--   The P2 M Ground Theory Heights  Heights is Radical Away iff is Radical rabinowitsch Ideal 06c1b40e5723 construction uses the P2 M Ground Theory Heights  Heights is Radical Away iff is Radical rabinowitsch Ideal 06c1b40e5723 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L113-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L113-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_isRadicalAway_iff_isRadical_rabinowitschIdeal_06c1b40e5723 (K : Ideal (MvPolynomial ι R))
    (g : MvPolynomial ι R) : IsRadicalAway K g ↔ (rabinowitschIdeal K g).IsRadical := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRadicalAway_iff_isRadical_rabinowitschIdeal» := P2M_GroundTheory_Heights__Heights_isRadicalAway_iff_isRadical_rabinowitschIdeal_06c1b40e5723
