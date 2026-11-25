-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_hasFDerivAt_eval
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:28.146874+00:00
-- url     : https://prove2.me/theorems/a0ea1612-6bbd-5e21-b119-3921fe95c49b
-- title:
--   Arakelov Geometry: adens has FDeriv At eval
-- statement:
--   The Arakelov Geometry construction uses the adens has FDeriv At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L14-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval (F : MvPolynomial J ℂ) (z : J → ℂ) :
    HasFDerivAt (fun w => eval w F)
      (∑ i, eval z (pderiv i F) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i) z := by sorry
