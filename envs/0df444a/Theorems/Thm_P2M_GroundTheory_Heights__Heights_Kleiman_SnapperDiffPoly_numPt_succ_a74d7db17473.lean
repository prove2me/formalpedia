-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:50.762604+00:00
-- url     : https://prove2.me/theorems/797462d0-eb2c-59d1-8146-6bea6eece50c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt succ a74d7db17473: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt succ a74d7db17473
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt succ a74d7db17473 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt succ a74d7db17473 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L24-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473 {t : ℕ} (n : Fin t → ℕ) (c : ℤ) :
    numPt n (c + 1) = numPt n c + Pi.single (Fin.last t) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«numPt_succ» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_succ_a74d7db17473
