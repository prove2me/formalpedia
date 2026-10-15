-- Prove2me | Theorems.Thm_ThreeSum_CostLedger_queryTerms_log_bound
-- name    : ThreeSum.CostLedger.queryTerms_log_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:45:09.66885+00:00
-- url     : https://prove2.me/theorems/b9c495ee-7a55-4f02-bf1c-d30ceef9583c
-- title:
--   Logarithmic query bound including switch rounding
-- statement:
--   Let $m=\lfloor\log_2n\rfloor$, $u=2\lfloor\lfloor\sqrt[3]{m}\rfloor/2\rfloor$, $J=20\lfloor m/(100u)\rfloor$, and $\mu=Ju>0$. For $j\le\lfloor13J/20\rfloor$, put $r=(J-j)u$ and let $q\le\lfloor r/2\rfloor$ be the least integer for which
--   $$(291J+1000j)r^3\le10(J-j)(799qr^2+72q^2r+24q^3).$$
--   The number of query terms at this depth is $Q_{n,j}=\binom rq$. Its natural logarithm obeys
--   $$\ln Q_{n,j}\le\mu\ln2\left(\frac{277}{1000}\frac{1291}{1000}\right)+9\frac{277}{1000}\ln2.$$
--
--   The additive term records the rounding allowance for the executable integer switch. This gives a uniform finite bound on the query count at every admissible depth, without replacing the switch by a real-valued idealization.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/CostLedger.lean#L181-L213

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
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.Switch
end ThreeSum.Switch

theorem ThreeSum.CostLedger.queryTerms_log_bound : ∀ {n j : Nat}
  (hmu : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (ThreeSum.Scales.mu n))
  (hj : @LE.le.{0} Nat instLENat j (ThreeSum.Switch.terminalDepth n)),
  @LE.le.{0} Real Real.instLE (Real.log (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.CostLedger.queryTerms n j)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.mu n))
          (Real.log
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ThreeSum.Parameters.boxSaving)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              ThreeSum.Parameters.bandShift))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 9)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
          ThreeSum.Parameters.entropyRatio)
        (Real.log
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))) := by
  sorry
