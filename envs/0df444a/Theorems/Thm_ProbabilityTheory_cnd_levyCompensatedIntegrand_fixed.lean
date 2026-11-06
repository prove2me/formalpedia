-- Prove2me | Theorems.Thm_ProbabilityTheory_cnd_levyCompensatedIntegrand_fixed
-- name    : ProbabilityTheory.cnd_levyCompensatedIntegrand_fixed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:54:18.889201+00:00
-- url     : https://prove2.me/theorems/4ffd0ac5-dd7c-4039-bf57-825f40cb3d18
-- title:
--   LeanLevy: ProbabilityTheory.cnd_levyCompensatedIntegrand_fixed
-- statement:
--   For fixed `x`, the compensated integrand `ξ ↦ f(ξ, x)` is conditionally negative Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L455

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

theorem ProbabilityTheory.cnd_levyCompensatedIntegrand_fixed : ∀ (x : Real), ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ => ProbabilityTheory.levyCompensatedIntegrand ξ x := by sorry
