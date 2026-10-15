-- Prove2me | Theorems.Thm_ThreeSum_Switch_actual_switch_certified
-- name    : ThreeSum.Switch.actual_switch_certified
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:26:28.379026+00:00
-- url     : https://prove2.me/theorems/6a3bf167-1858-498e-a77c-534d633bce79
-- title:
--   The integer reporting switch satisfies both analytic cost bounds
-- statement:
--   For input size $n$, let $J$ and $\mu_0$ be the prescribed block count and microblock size, with total size $\mu=\mu(n)>0$. Suppose $j\le\lfloor13J/20\rfloor$, set $r=(J-j)\mu_0$, and let $q$ be the least integer $0\le q\le r/2$ satisfying
--   $$
--   (291J+1000j)r^3\le10(J-j)(799qr^2+72q^2r+24q^3).
--   $$
--   Define $a=j/J$, $t=q/r$, binary entropy $H_2$, $\eta=277/1000$, and $\gamma(t)=256H_2(1/256)-256H_2((1-t)/256)$. Then
--   $$
--   0\le t\le\tfrac12,\qquad
--   \tfrac{191}{1000}\le-\tfrac1{10}-a+(1-a)\gamma(t),\qquad
--   (1-a)H_2(t)<\tfrac{1291}{1000}\eta+\frac{9\eta}{\mu}.
--   $$
--   Thus the actual integer switch simultaneously supplies the required box saving and entropy charge, including its rounding allowance.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Switch.lean#L219-L241

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Parameters_phi_le_gamma
import Theorems.Thm_ThreeSum_Parameters_switch_entropy_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales

theorem ThreeSum.Switch.actual_switch_certified : ∀ {n j : Nat}
  (hmu : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (ThreeSum.Scales.mu n))
  (hj : @LE.le.{0} Nat instLENat j (ThreeSum.Switch.terminalDepth n)),
  have a :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast j)
      (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)));
  have t :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Switch.actualSwitch n j))
      (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Switch.residualSize n j));
  And
    (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      t)
    (And
      (@LE.le.{0} Real Real.instLE ThreeSum.Parameters.boxSaving
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              ThreeSum.Parameters.bandShift)
            a)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
            (ThreeSum.Parameters.gamma t))))
      (@LT.lt.{0} Real Real.instLT
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
          (ThreeSum.Parameters.entropy t))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ThreeSum.Parameters.boxSaving)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                ThreeSum.Parameters.bandShift)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 9)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
              ThreeSum.Parameters.entropyRatio)
            (@Nat.cast.{0} Real Real.instNatCast (ThreeSum.Scales.mu n)))))) := by
  sorry
