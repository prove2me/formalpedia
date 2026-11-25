-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_mul_mem_coneRing_int_fin
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_mem_coneRing_int_fin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:18.662972+00:00
-- url     : https://prove2.me/theorems/2d0889ef-9d95-505c-b422-ab1ef20500bd
-- title:
--   Arakelov Geometry: exists nat mul mem cone Ring int fin
-- statement:
--   The Arakelov Geometry construction uses the exists nat mul mem cone Ring int fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L57-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L57-L76

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_mem_coneRing_int_fin (y : ι → Ω) (f : ℕ → (Polynomial Ω)) (hf : ∀ i, f i ∈ coneRing ℚ y) (d : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < d, (n : (Polynomial Ω)) * f i ∈ coneRing ℤ y := by sorry
