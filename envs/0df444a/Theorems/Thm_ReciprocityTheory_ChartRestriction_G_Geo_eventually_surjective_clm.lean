-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eventually_surjective_clm
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eventually_surjective_clm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:18.162195+00:00
-- url     : https://prove2.me/theorems/7780f692-50a0-45c7-941f-0da968e8d5fd
-- title:
--   Geo: eventually surjective clm
-- statement:
--   The Geo construction uses the eventually surjective clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeK.lean#L11-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeK.lean#L11-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Set Filter Topology Module
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.eventually_surjective_clm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {Y : Type*} [TopologicalSpace Y] {A : Y → (Fin e → ℂ) →L[ℂ] F}
    {y0 : Y} (hA : ContinuousAt A y0) (h0 : Function.Surjective (A y0)) :
    ∀ᶠ y in 𝓝 y0, Function.Surjective (A y) := by sorry
