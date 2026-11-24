-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mul_mem_sec
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.mul_mem_sec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:15.58911+00:00
-- url     : https://prove2.me/theorems/7a12faf3-e307-4d62-a63a-b895061d8c6f
-- title:
--   Trace Norm Bounds: mul mem sec
-- statement:
--   The Trace Norm Bounds construction uses the mul mem sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L74-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.mul_mem_sec {o : Type*} [CommRing o] [Algebra o Ω] {ι : Type*} (x : ι → Ω) {d d' : ℕ}
    {s t : Ω} (hs : s ∈ sec o x d) (ht : t ∈ sec o x d') : s * t ∈ sec o x (d + d') := by sorry
