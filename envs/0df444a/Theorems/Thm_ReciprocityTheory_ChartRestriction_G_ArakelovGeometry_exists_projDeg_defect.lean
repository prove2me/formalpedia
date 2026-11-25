-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_projDeg_defect
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_projDeg_defect
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:19.775937+00:00
-- url     : https://prove2.me/theorems/2623a121-d28a-533b-904a-1a71bd7b7948
-- title:
--   Arakelov Geometry: exists proj Deg defect
-- statement:
--   The Arakelov Geometry construction uses the exists proj Deg defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HSClosing.lean#L88-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/HSClosing.lean#L88-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
attribute [instance] GDatum.fieldΩ GDatum.charΩ GDatum.fintypeκ

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_projDeg_defect (I : AllFam) (D : ℕ) (hA : StepA I D) (hT : StepT D)
    (hB : StepB I D) (hN : StepN D) (hM : StepM D) (hC : StepC I D) (d : GDatum D) :
    ∃ (A : Matrix (Ix d.κ) (Ix d.κ) ℚ) (e : Fin (D + 1) → Ix d.κ), IsInvMat A ∧
      IsProjFrame (matAct A d.x) e ∧
      (fun n => defect I D d.x d.m d.μ n -
        (projDeg (matAct A d.x) e : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D := by sorry
