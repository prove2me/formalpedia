-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeDepth_log_ratio_tendsto_zero
-- name    : ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:34:56.392402+00:00
-- url     : https://prove2.me/theorems/c2b29f33-0e6b-498e-8777-698527610573
-- title:
--   The selected prime-chain depth is sublogarithmic
-- statement:
--   Let $R(n)$ be the radix schedule fixed by the construction. Define the prime-window size $Y(n)=2^{\lfloor\sqrt{\lfloor\log_2 n\rfloor}\rfloor+1}$ and the chain depth $D(n)=\log_{4Y(n)}^{\mathrm{nat}}(\lfloor R(n)/4\rfloor)$, using natural-number division and logarithm. Then
--
--   $$\lim_{n\to\infty}\frac{D(n)}{\log n}=0,$$
--
--   where the denominator is the real natural logarithm. This controls the length of the chosen prime chain relative to input bit length, a scale estimate used to bound repeated prime-dependent overhead.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L596-L610

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Scales.primeDepth_log_ratio_tendsto_zero : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.primeDepth ThreeSum.Scales.radix n))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  sorry
