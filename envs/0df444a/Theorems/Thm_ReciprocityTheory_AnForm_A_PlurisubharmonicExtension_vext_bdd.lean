-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_bdd
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:11.565586+00:00
-- url     : https://prove2.me/theorems/12161696-2298-4aec-9c60-0898999ad91b
-- title:
--   Plurisubharmonic Extension: vext bdd
-- statement:
--   The Plurisubharmonic Extension construction uses the vext bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExt.lean#L117-L121

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

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_bdd {K : Set (Fin D → ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M, ∀ y ∈ K, vext U S u κ y ≤ M := by sorry
