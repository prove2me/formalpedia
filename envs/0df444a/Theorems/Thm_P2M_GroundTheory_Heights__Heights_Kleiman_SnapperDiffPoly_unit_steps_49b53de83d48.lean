-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:19.243742+00:00
-- url     : https://prove2.me/theorems/34333579-bdb6-450c-8fdf-e883d71e9905
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly unit steps 49b53de83d48: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly unit steps 49b53de83d48
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly unit steps 49b53de83d48 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly unit steps 49b53de83d48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L88-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L88-L177

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48 {t D : ℕ} (g : (Fin t → ℕ) → ℤ → ℚ)
    (hc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c))
    (hj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c)) :
    IsNumPolyLT t (D + 1) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«unit_steps» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48
