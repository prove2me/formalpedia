-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsProjFrame_isRatProjFrame
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsProjFrame.isRatProjFrame
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:50.871574+00:00
-- url     : https://prove2.me/theorems/6bd33b4a-581c-410e-b13e-90b036411e7a
-- title:
--   Is Proj Frame: is Rat Proj Frame
-- statement:
--   The Is Proj Frame construction uses the is Rat Proj Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L231-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L231-L232

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsProjFrame.isRatProjFrame {x : κ → Ω} {e : Fin (D + 1) → κ} (h : IsProjFrame x e) :
    IsRatProjFrame x e := by sorry
