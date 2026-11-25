-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:48.568775+00:00
-- url     : https://prove2.me/theorems/4c7674d6-2cae-46a9-a86e-7ff286219f05
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists poly back Diff pow 32b050b07dc7: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists poly back D
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists poly back Diff pow 32b050b07dc7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists poly back Diff pow 32b050b07dc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsPolyBackDiffPow.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsPolyBackDiffPow.lean#L9-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsPolyBackDiffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7 (n : ℕ) :
    ∃ P : Polynomial ℚ, ∀ t : ℚ, P.eval t - P.eval (t - 1) = t ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_poly_backDiff_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_poly_backDiff_pow_32b050b07dc7
