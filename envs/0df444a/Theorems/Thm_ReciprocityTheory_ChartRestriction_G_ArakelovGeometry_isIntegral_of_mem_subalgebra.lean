-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isIntegral_of_mem_subalgebra
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegral_of_mem_subalgebra
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:49.672702+00:00
-- url     : https://prove2.me/theorems/252ae19d-bed4-423e-ac80-bed8a97dff49
-- title:
--   Arakelov Geometry: is Integral of mem subalgebra
-- statement:
--   The Arakelov Geometry construction uses the is Integral of mem subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L78-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsNatMulMemConeRingIntFin.lean#L78-L78

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isIntegral_of_mem_subalgebra {S : Subalgebra ℤ (Polynomial Ω)} {v : (Polynomial Ω)} (hv : v ∈ S) : IsIntegral S v := by sorry
