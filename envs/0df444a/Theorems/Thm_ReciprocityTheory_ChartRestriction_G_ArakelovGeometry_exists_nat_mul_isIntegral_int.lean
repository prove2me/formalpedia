-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_mul_isIntegral_int
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_isIntegral_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:21.332476+00:00
-- url     : https://prove2.me/theorems/fd38797b-e7cb-5be5-8cb2-28082c727255
-- title:
--   Arakelov Geometry: exists nat mul is Integral int
-- statement:
--   The Arakelov Geometry construction uses the exists nat mul is Integral int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L80-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L80-L115

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_isIntegral_int (y : ι → Ω) (a : (Polynomial Ω)) (ha : IsIntegral (coneRing ℚ y) a) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral (coneRing ℤ y) ((n : (Polynomial Ω)) * a) := by sorry
