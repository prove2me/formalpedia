-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_aeval_mem_field
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.aeval_mem_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:40.71075+00:00
-- url     : https://prove2.me/theorems/14d0e9c1-6336-46ad-a5fa-5519da19074e
-- title:
--   Trace Norm Bounds: aeval mem field
-- statement:
--   The Trace Norm Bounds construction uses the aeval mem field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L34-L37

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.aeval_mem_field {o σ : Type*} [CommRing o] [Algebra o Ω] (F : IntermediateField ℚ Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F := by sorry
