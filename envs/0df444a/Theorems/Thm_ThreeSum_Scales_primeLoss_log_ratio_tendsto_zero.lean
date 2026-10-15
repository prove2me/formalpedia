-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeLoss_log_ratio_tendsto_zero
-- name    : ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:39:55.178276+00:00
-- url     : https://prove2.me/theorems/6fe2fa2f-1610-4f02-9c26-0c86c0304060
-- title:
--   The prime-modulus loss has logarithmic exponent zero
-- statement:
--   Let $y(n)=\operatorname{primeWindow}(n)$ and $M(n)=\operatorname{radix}(n)$ be the executable prime-window and radix functions. Define $d(n)$ as the natural logarithm to base $4y(n)$ of the natural quotient $M(n)/4$, as in the computed prime depth. The modulus-loss factor is $L(n)=32y(n)4^{d(n)}$. Then
--
--   $$
--   \lim_{n\to\infty}\frac{\log L(n)}{\log n}=0.
--   $$
--
--   This shows that the actual integer modulus loss can be absorbed into arbitrarily small exponent slack, without assuming a separate asymptotic bound on that loss.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L612-L625

import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_primeDepth_log_ratio_tendsto_zero


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.primeLoss ThreeSum.Scales.radix n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  sorry
