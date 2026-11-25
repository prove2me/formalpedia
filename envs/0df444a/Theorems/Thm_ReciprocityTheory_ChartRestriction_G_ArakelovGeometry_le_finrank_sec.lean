-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_finrank_sec
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_finrank_sec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:32:37.24215+00:00
-- url     : https://prove2.me/theorems/01a8111f-65b6-4e47-a120-f04aa9febabb
-- title:
--   Arakelov Geometry: le finrank sec
-- statement:
--   The Arakelov Geometry construction uses the le finrank sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ChooseLePowDivFactorial.lean#L112-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ChooseLePowDivFactorial.lean#L112-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_finrank_sec (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    ∃ k : ℕ, ∀ n, projDeg x e * (n + D).choose D ≤ finrank ℤ (sec ℤ x (n + k)) := by sorry
