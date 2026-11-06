-- Prove2me | Theorems.Thm_ProbabilityTheory_toReal_mul_integral_prmPieceLaw
-- name    : ProbabilityTheory.toReal_mul_integral_prmPieceLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:53:40.08083+00:00
-- url     : https://prove2.me/theorems/1316840d-1a73-491c-8e14-ab349964c01c
-- title:
--   Poisson piece law scaling for signed integrals
-- statement:
--   The measure of a finite Poisson partition piece times its normalised mark-law integral equals the original restricted integral, including the zero-measure case.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean lines 459–467, private toReal_mul_integral_prmPieceLaw; source exact.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.toReal_mul_integral_prmPieceLaw
    {E : Type} [MeasurableSpace E] {m : Measure E} [SigmaFinite m]
    [Nonempty E] {k : ℕ} (g : E → ℝ) :
    (m (prmPiece m k)).toReal * ∫ x, g x ∂(prmPieceLaw m k) =
      ∫ x in prmPiece m k, g x ∂m := by sorry
