-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_inj_cover
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_inj_cover
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:03.149436+00:00
-- url     : https://prove2.me/theorems/cb4c369e-b26b-53bd-af01-9cb0511f3cb9
-- title:
--   Geo: exists inj cover
-- statement:
--   The Geo construction uses the exists inj cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L75-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L75-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
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
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_inj_cover {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) (hO : IsOpen O) :
    ∃ W : ℕ → Set (Fin e → ℂ), (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ O) ∧ (∀ n, InjOn Q (W n)) ∧
      ⋃ n, W n = O := by sorry
