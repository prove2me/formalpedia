-- Prove2me | Theorems.Thm_ProbabilityTheory_IsConditionallyNegativeDefinite_add
-- name    : ProbabilityTheory.IsConditionallyNegativeDefinite.add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:48:42.592213+00:00
-- url     : https://prove2.me/theorems/60b7398c-d82f-4673-a5ff-50302dab2cf0
-- title:
--   LeanLevy: ProbabilityTheory.IsConditionallyNegativeDefinite.add
-- statement:
--   The sum of two conditionally negative definite functions is conditionally negative Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L311

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

theorem ProbabilityTheory.IsConditionallyNegativeDefinite.add : ∀ {ψ₁ ψ₂ : Real → Complex},
  ProbabilityTheory.IsConditionallyNegativeDefinite ψ₁ →
    ProbabilityTheory.IsConditionallyNegativeDefinite ψ₂ →
      ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ =>
        @HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (ψ₁ ξ) (ψ₂ ξ) := by sorry
