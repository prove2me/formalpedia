-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186
-- name    : P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:57.363443+00:00
-- url     : https://prove2.me/theorems/a2a220fd-86f2-43c1-91a4-585925b16641
-- title:
--   P2 M Ground Theory Heights  Heights Tube Collar Comparison cont Diff At log Sq comp a77eed4f6186: P2 M Ground Theory Heights  Heights Tube Collar Comparison cont Diff At log Sq comp a77eed4f6186
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Collar Comparison cont Diff At log Sq comp a77eed4f6186 construction uses the P2 M Ground Theory Heights  Heights Tube Collar Comparison cont Diff At log Sq comp a77eed4f6186 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarCompare.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarCompare.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeCollarCompare
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeCollarComparison

theorem P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (Fin m) ℂ)
    (x : Fin n → ℂ) (hP : eval (A *ᵥ x) P ≠ 0) :
    ContDiffAt ℝ 2 (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeCollarComparison».«contDiffAt_logSq_comp» := P2M_GroundTheory_Heights__Heights_TubeCollarComparison_contDiffAt_logSq_comp_a77eed4f6186
