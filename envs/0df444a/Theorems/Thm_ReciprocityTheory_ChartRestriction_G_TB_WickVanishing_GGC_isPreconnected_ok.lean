-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_isPreconnected_ok
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:41.097738+00:00
-- url     : https://prove2.me/theorems/1ff5e58a-ab35-4fdc-bad7-b6d653f6480a
-- title:
--   GGC: is Preconnected ok
-- statement:
--   The GGC construction uses the is Preconnected ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L219-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L219-L246

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
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_ok {ι : Type*} [Fintype ι] :
    IsPreconnected {y : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i, Ok p0 (y i)} := by sorry
