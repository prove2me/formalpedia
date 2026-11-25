-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_projDeg_scaleOff
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.projDeg_scaleOff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:11:29.828679+00:00
-- url     : https://prove2.me/theorems/a1699496-17f0-58ee-8ae4-623135116260
-- title:
--   Arakelov Geometry: proj Deg scale Off
-- statement:
--   The Arakelov Geometry construction uses the proj Deg scale Off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L181-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L181-L187

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.projDeg_scaleOff (x : κ → Ω) (e : Fin (D + 1) → κ) (he : Function.Injective e) {m : ℕ}
    (hm : 0 < m) : projDeg (scaleOff e m x) e = projDeg x e := by sorry
