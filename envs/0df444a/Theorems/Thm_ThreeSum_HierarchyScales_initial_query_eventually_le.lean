-- Prove2me | Theorems.Thm_ThreeSum_HierarchyScales_initial_query_eventually_le
-- name    : ThreeSum.HierarchyScales.initial_query_eventually_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:45:22.927823+00:00
-- url     : https://prove2.me/theorems/fcec8026-5798-45eb-98f7-c6981a84e15c
-- title:
--   Initial hierarchy queries have entropy exponent $H(1/25)/5$
-- statement:
--   For each input size $n$, use the integer hierarchy schedule $m=\lfloor\log_2n\rfloor$, $u=2\lfloor\lfloor\sqrt[3]{m}\rfloor/2\rfloor$, $J=20\lfloor m/(100u)\rfloor$, and $\mu=Ju$. Let $q$ be the depth-zero cubic switch: the least $q\le\lfloor\mu/2\rfloor$ satisfying $291J\mu^3\le10J(799q\mu^2+72q^2\mu+24q^3)$, with value zero if there is no candidate. Natural division by zero uses value zero in the schedule. Write $Q_{n,0}=\binom\mu q$ and let $H$ denote binary entropy.
--
--   For every real $\varepsilon>0$, there is $N$ such that
--   $$Q_{n,0}\le n^{H(1/25)/5+\varepsilon}\qquad(n\ge N).$$
--
--   This isolates the smaller exponent of the initial query layer in the actual rounded hierarchy.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HierarchyScales.lean#L235-L255

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum_Switch_actual_switch_certified


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

theorem ThreeSum.HierarchyScales.initial_query_eventually_le : ∀ {d : Real}
  (hd : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d),
  @Filter.Eventually.{0} Nat
    (fun (n : Nat) =>
      @LE.le.{0} Real Real.instLE
        (@Nat.cast.{0} Real Real.instNatCast
          (ThreeSum.CostLedger.queryTerms n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast n)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (ThreeSum.Parameters.entropy ThreeSum.Parameters.initialTheta)
              (@OfNat.ofNat.{0} Real (nat_lit 5)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
            d)))
    (@Filter.atTop.{0} Nat Nat.instPreorder) := by
  sorry
