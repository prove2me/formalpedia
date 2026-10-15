-- Prove2me | Theorems.Thm_ThreeSum_StageBounds_terminalChoices_log_rate
-- name    : ThreeSum.StageBounds.terminalChoices_log_rate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:02:39.032079+00:00
-- url     : https://prove2.me/theorems/178f2885-1446-4da7-b431-715cb7247982
-- title:
--   Logarithmic growth rate of terminal completion choices
-- statement:
--   For input size $n$, let $J(n)$ be the construction's block count and $\mu_0(n)$ its microblock size. Define the terminal depth $D(n)=\lfloor13J(n)/20\rfloor$, residual size $r(n)=(J(n)-D(n))\mu_0(n)$, and terminal-choice bound $T(n)=2^{r(n)}$. For the prescribed integer scale schedule,
--   $$
--   \lim_{n\to\infty}\frac{\log T(n)}{\log n}
--   =\frac{1-13/20}{5}=\frac7{100}.
--   $$
--   All logarithms are natural logarithms. This determines the exponent contributed by the terminal completion bound in the cost ledger.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/StageBounds.lean#L177-L190

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum_Switch_terminal_fraction_exact


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

theorem ThreeSum.StageBounds.terminalChoices_log_rate : @Filter.Tendsto.{0, 0} Nat Real
  (fun (n : Nat) =>
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.StageBounds.terminalChoices n)))
      (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
  (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@nhds.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ThreeSum.Parameters.terminalFraction)
      (@OfNat.ofNat.{0} Real (nat_lit 5)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  sorry
