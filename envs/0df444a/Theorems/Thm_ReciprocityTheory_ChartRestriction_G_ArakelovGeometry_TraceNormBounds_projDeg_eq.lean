-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_projDeg_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.projDeg_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:59.605532+00:00
-- url     : https://prove2.me/theorems/ffdecb53-7302-4b7f-9132-b9688f2a12b2
-- title:
--   Trace Norm Bounds: proj Deg eq
-- statement:
--   The Trace Norm Bounds construction uses the proj Deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjectiveFrameCoordNeZero.lean#L130-L132

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.projDeg_eq (x : κ → Ω) (e : Fin (D + 1) → κ) :
    projDeg x e = finrank (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by sorry
