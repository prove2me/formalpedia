-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_isPreconnected_det_ne
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_det_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:37.955497+00:00
-- url     : https://prove2.me/theorems/b738cd3c-c68e-496e-8e6e-4976556b652a
-- title:
--   GGC: is Preconnected det ne
-- statement:
--   The GGC construction uses the is Preconnected det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L9-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L9-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Polynomial

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_det_ne {ι : Type*} [Fintype ι] {n : ℕ} (V : Set (ι → Matrix (Fin n) (Fin n) ℂ))
    (hV : ∀ a ∈ V, ∀ b ∈ V, ∀ z : ℂ, (1 - z) • a + z • b ∈ V) :
    IsPreconnected {x | x ∈ V ∧ ∀ i, (x i).det ≠ 0} := by sorry
