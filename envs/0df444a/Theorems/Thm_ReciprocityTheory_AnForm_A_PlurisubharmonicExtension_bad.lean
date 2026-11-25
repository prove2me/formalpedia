-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_bad
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.bad
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:31.343803+00:00
-- url     : https://prove2.me/theorems/0ac18ade-785b-455b-b380-09f398fd4c28
-- title:
--   Plurisubharmonic Extension: bad
-- statement:
--   The Plurisubharmonic Extension construction uses the bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L254-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L254-L312

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}
variable (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
include hU hU1 hc hpsh hg

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.bad {z w : Fin D → ℂ} (hzU : z ∈ U) (hzA : z ∈ coordDiv S)
    (hD : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) :
    vext U S u κ z ≤ circleAverage (fun ζ => vext U S u κ (z + ζ • w)) 0 1 := by sorry
