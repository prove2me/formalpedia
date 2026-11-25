-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:24.010422+00:00
-- url     : https://prove2.me/theorems/2b10d5a1-6dbd-586b-84b9-205d5407bbbf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mvpoly back Diff 96559c510566: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mvpoly back D
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mvpoly back Diff 96559c510566 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mvpoly back Diff 96559c510566 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsPolyBackDiffPow.lean#L22-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsPolyBackDiffPow.lean#L22-L55

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566 {K : Type} [DecidableEq K] (k : K) (q : MvPolynomial K ℚ) :
    ∃ R : MvPolynomial K ℚ, ∀ x : K → ℚ, eval x R - eval (x - Pi.single k 1) R = eval x q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_mvpoly_backDiff» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566
