-- Prove2me | Theorems.Thm_ProbabilityTheory_IsConditionallyNegativeDefinite_smul_nonneg
-- name    : ProbabilityTheory.IsConditionallyNegativeDefinite.smul_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:48:58.007247+00:00
-- url     : https://prove2.me/theorems/43f13cc7-0271-467b-946a-4bb2b8a718be
-- title:
--   LeanLevy: ProbabilityTheory.IsConditionallyNegativeDefinite.smul_nonneg
-- statement:
--   A non-negative real scaling of a conditionally negative definite function is Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L333

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

theorem ProbabilityTheory.IsConditionallyNegativeDefinite.smul_nonneg : ∀ {a : Real} {ψ : Real → Complex},
  ProbabilityTheory.IsConditionallyNegativeDefinite ψ →
    @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) a →
      ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ =>
        @HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑a) (ψ ξ) := by sorry
