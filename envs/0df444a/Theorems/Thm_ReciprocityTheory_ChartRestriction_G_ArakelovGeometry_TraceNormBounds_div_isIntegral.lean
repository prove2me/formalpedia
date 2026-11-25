-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_isIntegral
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.div_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:16.83684+00:00
-- url     : https://prove2.me/theorems/76867e91-498e-437a-9e18-11d96cdac578
-- title:
--   Trace Norm Bounds: div is Integral
-- statement:
--   The Trace Norm Bounds construction uses the div is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L42-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L42-L65

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (i : κ) :
    IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by sorry
