-- Prove2me | Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
-- name    : ProbabilityTheory.LevyKhintchineTriple.exponent_def
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:20:41.137987+00:00
-- url     : https://prove2.me/theorems/674959c0-4e8d-4dbc-b462-af9200c163e7
-- title:
--   LeanLevy: ProbabilityTheory.LevyKhintchineTriple.exponent_def
-- statement:
--   Definitional unfolding of `LevyKhintchineTriple.exponent`. The exact theorem type was printed from the pinned compiled Lean environment; the source proof remains to be transplanted and remotely verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L5194

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem ProbabilityTheory.LevyKhintchineTriple.exponent_def :
  ∀ (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ),
  T.exponent ξ =
    ↑T.drift * ↑ξ * Complex.I - ↑↑T.gaussianVariance * ↑ξ ^ 2 / 2 +
      ∫ (x : ℝ), ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure := by sorry
