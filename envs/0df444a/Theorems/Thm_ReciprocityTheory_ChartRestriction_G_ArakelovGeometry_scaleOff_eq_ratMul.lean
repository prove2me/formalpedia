-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_scaleOff_eq_ratMul
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.scaleOff_eq_ratMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:41.962076+00:00
-- url     : https://prove2.me/theorems/e77daf6b-4026-4624-a2e8-1161eb9126de
-- title:
--   Arakelov Geometry: scale Off eq rat Mul
-- statement:
--   The Arakelov Geometry construction uses the scale Off eq rat Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L156-L160

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.scaleOff_eq_ratMul (x : κ → Ω) (e : Fin (D + 1) → κ) (m : ℕ) (i : κ) :
    scaleOff e m x i = algebraMap ℚ Ω (if i ∈ Set.range e then 1 else (m : ℚ)) * x i := by sorry
