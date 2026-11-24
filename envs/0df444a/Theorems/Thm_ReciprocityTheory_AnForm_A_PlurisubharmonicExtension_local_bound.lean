-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_local_bound
-- name    : ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.local_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:16.111711+00:00
-- url     : https://prove2.me/theorems/a0bb6afe-54b0-4e41-8dbf-5d50e29ea37e
-- title:
--   Plurisubharmonic Extension: local bound
-- statement:
--   The Plurisubharmonic Extension construction uses the local bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L188-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshExtB.lean#L188-L310

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
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}

theorem ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.local_bound (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {p : Fin D → ℂ} (hp : p ∈ U) : ∃ ρ > 0, ∃ M, ∀ z ∈ ball p ρ \ coordDiv S, u z ≤ M := by sorry
