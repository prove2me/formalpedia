-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_ratMul_scaleOff
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_ratMul_scaleOff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:43.205217+00:00
-- url     : https://prove2.me/theorems/26584d20-24b2-4a09-8a68-e7b717e214dd
-- title:
--   Arakelov Geometry: eq rat Mul scale Off
-- statement:
--   The Arakelov Geometry construction uses the eq rat Mul scale Off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L163-L168

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
open Classical

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_ratMul_scaleOff (x : κ → Ω) (e : Fin (D + 1) → κ) {m : ℕ} (hm : 0 < m) (i : κ) :
    x i = algebraMap ℚ Ω (if i ∈ Set.range e then 1 else (m : ℚ)⁻¹) * scaleOff e m x i := by sorry
