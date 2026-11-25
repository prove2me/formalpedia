-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_lap_fiber
-- name    : ReciprocityTheory.AnForm.A.lap_fiber
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:53.52771+00:00
-- url     : https://prove2.me/theorems/c31273f0-5227-4d02-a6ec-7bbdcc987801
-- title:
--   A: lap fiber
-- statement:
--   The A construction uses the lap fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LeviOneEqLaplacianThm.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/LeviOneEqLaplacianThm.lean#L79-L98

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section

theorem ReciprocityTheory.AnForm.A.lap_fiber {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℂ × E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : ℂ) (p : E) :
    Δ (fun w : ℂ => u (w, p)) z = fderiv ℝ (fderiv ℝ u) (z, p) (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) (z, p) (Complex.I, 0) (Complex.I, 0) := by sorry
