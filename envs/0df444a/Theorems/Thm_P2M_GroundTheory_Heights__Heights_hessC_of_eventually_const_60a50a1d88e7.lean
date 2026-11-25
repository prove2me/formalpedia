-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7
-- name    : P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:24.823459+00:00
-- url     : https://prove2.me/theorems/ae15e165-57b2-49e1-90b9-b837f2e0bd1c
-- title:
--   P2 M Ground Theory Heights  Heights hess C of eventually const 60a50a1d88e7: P2 M Ground Theory Heights  Heights hess C of eventually const 60a50a1d88e7
-- statement:
--   The P2 M Ground Theory Heights  Heights hess C of eventually const 60a50a1d88e7 construction uses the P2 M Ground Theory Heights  Heights hess C of eventually const 60a50a1d88e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessConst.lean#L13-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessConst
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
open MvPolynomial Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7 {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 y] fun _ => c) : hessC φ y = 0 ∧ hessC (fun z => φ z ^ 2 / 2) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hessC_of_eventually_const» := P2M_GroundTheory_Heights__Heights_hessC_of_eventually_const_60a50a1d88e7
