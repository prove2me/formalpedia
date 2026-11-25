-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd
-- name    : P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:17.921638+00:00
-- url     : https://prove2.me/theorems/13b7e291-9689-4a05-b70e-7347dbed2321
-- title:
--   P2 M Ground Theory Heights  Heights Tube Collar Comparison abs ma Dens collar le 25cd3edee1fd: P2 M Ground Theory Heights  Heights Tube Collar Comparison abs ma Dens collar le 25cd3edee1fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Collar Comparison abs ma Dens collar le 25cd3edee1fd construction uses the P2 M Ground Theory Heights  Heights Tube Collar Comparison abs ma Dens collar le 25cd3edee1fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarCompare.lean#L25-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeCollarCompare.lean#L25-L88

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

theorem P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hg : ContDiffAt ℝ 2 g (s y)) {c : ℝ}
    (hb : (hessC g (s y) + (c : ℂ) • 1).PosSemidef ∧ (-hessC g (s y) + (c : ℂ) • 1).PosSemidef) :
    |maDens (fun k => vecCons g (fun _ => euclPot) k ∘ s) y| ≤
      3 ^ (d + 1) * c * maDens (fun _ : Fin (d + 1) => euclPot ∘ s) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeCollarComparison».«abs_maDens_collar_le» := P2M_GroundTheory_Heights__Heights_TubeCollarComparison_abs_maDens_collar_le_25cd3edee1fd
