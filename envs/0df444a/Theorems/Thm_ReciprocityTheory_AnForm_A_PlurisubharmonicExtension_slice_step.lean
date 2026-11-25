-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_slice_step
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.slice_step
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:56.029703+00:00
-- url     : https://prove2.me/theorems/2385cc92-c057-4eb7-a22e-b3a7815f7917
-- title:
--   Plurisubharmonic Extension: slice step
-- statement:
--   The Plurisubharmonic Extension construction uses the slice step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L85-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L85-L177

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
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
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.slice_step (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {x : Fin D → ℂ} {j : Fin D} (hj : j ∈ S) {r : ℝ} (hr : 0 < r) (hxA : x ∉ coordDiv S)
    (hxj : ‖x j‖ < r) (hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • ej j ∈ U) :
    ∃ ζ ∈ sphere (0 : ℂ) r, u x ≤ u (x + ζ • ej j) := by sorry
