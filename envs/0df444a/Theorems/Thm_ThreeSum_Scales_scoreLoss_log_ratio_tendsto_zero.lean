-- Prove2me | Theorems.Thm_ThreeSum_Scales_scoreLoss_log_ratio_tendsto_zero
-- name    : ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:58.56098+00:00
-- url     : https://prove2.me/theorems/16422c21-01a8-45bd-b772-165b1c71ba48
-- title:
--   The accumulated score-loss factor is subpolynomial
-- statement:
--   Fix $k\in\mathbb N$. For input length $n$, let $m(n)=\operatorname{inputBits}(n)$, $y(n)=2^{\lfloor\sqrt{m(n)}\rfloor+1}$, and let $R(n)$ be the radix fixed by the integer scale construction. Define
--   $r(n)=\operatorname{ilog}_{4y(n)}(R(n)\mathbin{\mathrm{div}}4)$ and
--   $S_k(n)=\bigl(16(k+2)(m(n)+1)\bigr)^{r(n)}$. Then
--
--   $$
--   \lim_{n\to\infty}\frac{\log S_k(n)}{\log n}=0.
--   $$
--
--   The limit is along natural input lengths, and $k$ stays fixed. The integer logarithm uses the construction's zero convention at argument zero.
--
--   This shows that the explicit score loss accumulated across the selected prime chain contributes no positive constant to the final input-size exponent.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Scales.lean#L806-L829

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

theorem ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero : ∀ (k : Nat),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.scoreLoss k n)))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  sorry
