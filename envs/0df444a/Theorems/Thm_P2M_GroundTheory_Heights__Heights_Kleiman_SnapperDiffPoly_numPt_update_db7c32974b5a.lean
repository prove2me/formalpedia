-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:59:58.984512+00:00
-- url     : https://prove2.me/theorems/51b4cdba-289f-582e-a20c-a5242affcf65
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt update db7c32974b5a: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt update db7c32974b5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt update db7c32974b5a construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly num Pt update db7c32974b5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L31-L39

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a {t : ℕ} (n : Fin t → ℕ) (c : ℤ) (j : Fin t) :
    numPt (Function.update n j (n j + 1)) c = numPt n c + Pi.single j.castSucc 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«numPt_update» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_numPt_update_db7c32974b5a
