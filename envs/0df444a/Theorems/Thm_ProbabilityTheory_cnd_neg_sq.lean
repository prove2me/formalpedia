-- Prove2me | Theorems.Thm_ProbabilityTheory_cnd_neg_sq
-- name    : ProbabilityTheory.cnd_neg_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:54:37.515493+00:00
-- url     : https://prove2.me/theorems/c48ff378-08d3-4d21-8e42-425877f9a965
-- title:
--   LeanLevy: ProbabilityTheory.cnd_neg_sq
-- statement:
--   The negative square `ξ ↦ -ξ²` is conditionally negative definite: the cross term Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L385

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

theorem ProbabilityTheory.cnd_neg_sq : ProbabilityTheory.IsConditionallyNegativeDefinite fun ξ =>
  @Neg.neg Complex Complex.instNeg
    (@HPow.hPow Complex Nat Complex
      (@instHPow Complex Nat
        (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))
      (↑ξ) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by sorry
