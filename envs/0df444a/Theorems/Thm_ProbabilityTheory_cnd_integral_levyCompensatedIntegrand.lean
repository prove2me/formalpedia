-- Prove2me | Theorems.Thm_ProbabilityTheory_cnd_integral_levyCompensatedIntegrand
-- name    : ProbabilityTheory.cnd_integral_levyCompensatedIntegrand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:53:57.29725+00:00
-- url     : https://prove2.me/theorems/a9f72e9f-fbc9-4652-a2fe-20290da693ec
-- title:
--   LeanLevy: ProbabilityTheory.cnd_integral_levyCompensatedIntegrand
-- statement:
--   The integral of the compensated integrand against a Lévy measure is conditionally Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L500

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

theorem ProbabilityTheory.cnd_integral_levyCompensatedIntegrand : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν →
    ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ =>
      @MeasureTheory.integral Real Complex Complex.instNormedAddCommGroup
        (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
          instInnerProductSpaceRealComplex)
        Real.measurableSpace ν fun x => ProbabilityTheory.levyCompensatedIntegrand ξ x := by sorry
