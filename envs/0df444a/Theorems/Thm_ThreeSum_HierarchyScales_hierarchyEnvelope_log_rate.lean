-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_hierarchyEnvelope_log_rate
-- name    : ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:09.568216+00:00
-- url     : https://prove2.me/theorems/2044a268-4c74-458c-bca9-e72f7991b384
-- title:
--   Logarithmic growth rate of the hierarchy envelope
-- statement:
--   Let $\mu(n)$ be the integer hierarchy size fixed by the scale construction, and let $C,B\in\mathbb R$ be arbitrary constants. Define
--   $H_{C,B}(n)=(\mu(n)+1)\exp(\mu(n)(\log2)C+B)$. As natural-number input sizes tend to infinity,
--
--   $$
--   \lim_{n\to\infty}\frac{\log H_{C,B}(n)}{\log n}=\frac C5.
--   $$
--
--   The constructed scale has $\mu(n)/\log n\to1/(5\log2)$; its additional factor $\mu(n)+1$ contributes zero to this logarithmic rate. The constants $C$ and $B$ have no sign restrictions.
--
--   The limit translates explicit hierarchy envelopes into power exponents in the original input size, supporting the cost bounds for summed boxes and queries.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HierarchyScales.lean#L114-L127

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch

theorem ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate : ∀ (C B : Real),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (ThreeSum.HierarchyScales.hierarchyEnvelope C B n))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  sorry
