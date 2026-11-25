-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_mul_coneMap_mem_int
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_coneMap_mem_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:08.68434+00:00
-- url     : https://prove2.me/theorems/f293eb1a-be33-4b35-ba67-1f9f09552a1d
-- title:
--   Arakelov Geometry: exists nat mul cone Map mem int
-- statement:
--   The Arakelov Geometry construction uses the exists nat mul cone Map mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L27-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L27-L55

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_coneMap_mem_int (y : ι → Ω) (p : MvPolynomial ι ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : (Polynomial Ω)) * coneMap ℚ y p ∈ coneRing ℤ y := by sorry
