-- Prove2me | Theorems.Thm_ProbabilityTheory_integrable_prmPieceLaw
-- name    : ProbabilityTheory.integrable_prmPieceLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:11:29.28729+00:00
-- url     : https://prove2.me/theorems/7fc3576f-6676-4f08-a79f-e04c0a56f189
-- title:
--   Integrability under the normalised Poisson partition-piece law
-- statement:
--   An integrable measurable real test function on an intensity partition piece remains integrable against its normalised mark law, including the zero-mass Dirac branch. Source ingredient for signed Campbell formula.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonPointFamily.lean, original private integrable_prmPieceLaw around lines 448–458.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal

theorem ProbabilityTheory.integrable_prmPieceLaw
    {E : Type*} [MeasurableSpace E] {m : Measure E}
    [SigmaFinite m] {k : ℕ} [Nonempty E]
    {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) :
    Integrable g (prmPieceLaw m k) := by sorry
