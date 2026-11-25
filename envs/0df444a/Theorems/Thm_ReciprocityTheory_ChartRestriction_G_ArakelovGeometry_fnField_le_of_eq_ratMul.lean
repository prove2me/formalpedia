-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fnField_le_of_eq_ratMul
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fnField_le_of_eq_ratMul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:08:51.554121+00:00
-- url     : https://prove2.me/theorems/86de61ed-7afb-4c4f-a566-be5ef56dfb59
-- title:
--   Arakelov Geometry: fn Field le of eq rat Mul
-- statement:
--   The Arakelov Geometry construction uses the fn Field le of eq rat Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L141-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L141-L151

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
variable {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fnField_le_of_eq_ratMul (x x' : ι → Ω) (c : ι → ℚ) (hc : ∀ i, x' i = algebraMap ℚ Ω (c i) * x i) :
    fnField x' ≤ fnField x := by sorry
