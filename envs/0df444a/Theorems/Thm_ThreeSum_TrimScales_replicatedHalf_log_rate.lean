-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_replicatedHalf_log_rate
-- name    : ThreeSum.TrimScales.replicatedHalf_log_rate
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:30:28.790103+00:00
-- url     : https://prove2.me/theorems/eb35ab7d-e481-4c94-b399-eb4bf217efde
-- title:
--   Replicating local costs scales their logarithmic rate by one fifth
-- statement:
--   Let $f:\mathbb N\to\mathbb N$ and $a\in\mathbb R$ satisfy
--
--   $$\lim_{h\to\infty}\frac{\log f(h)}{2h\log2}=a.$$
--
--   For input size $n$, let $b_n=\lfloor\log_2 n\rfloor$, let $h_n=\lfloor\lfloor\sqrt[3]{b_n}\rfloor/2\rfloor$, and let $J_n=20\lfloor b_n/(200h_n)\rfloor$, using natural-number division. Define the replicated cost $F(n)=f(h_n)^{J_n}$. Then
--
--   $$\lim_{n\to\infty}\frac{\log F(n)}{\log n}=\frac a5.$$
--
--   Real logarithms use the formalization's total convention $\log0=0$, so no positivity premise on $f$ is added. This transfers local exponential rates to the global replicated schedule.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/TrimScales.lean#L43-L62

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Scales
end ThreeSum.Scales

theorem ThreeSum.TrimScales.replicatedHalf_log_rate : ∀ {f : Nat → Nat} {a : Real}
  (hf :
    @Filter.Tendsto.{0, 0} Nat Real
      (fun (h : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (Real.log (@Nat.cast.{0} Real Real.instNatCast (f h)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@Nat.cast.{0} Real Real.instNatCast h))
            (Real.log
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        a)),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (n : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.TrimScales.replicatedHalf f n)))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) a
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))) := by
  sorry
