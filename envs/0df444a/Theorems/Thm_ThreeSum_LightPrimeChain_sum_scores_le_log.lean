-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_sum_scores_le_log
-- name    : ThreeSum.LightPrimeChain.sum_scores_le_log
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:54:23.278989+00:00
-- url     : https://prove2.me/theorems/4d3b65f1-7ab4-483b-9611-1d1115804907
-- title:
--   The sum of prime-extension scores is bounded by an integer logarithm
-- statement:
--   Let $p_0,\ldots,p_{s-1}$ be distinct primes with $p_i\ge y>1$, and let $q,n_A,n_B,n_C,M$ be natural numbers. Let $A,B,C$ be integer arrays on their respective index ranges. For each triple $(a,b,c)$ in those ranges, put $\delta=C(c)-B(b)-A(a)$ and assume $|\delta|\le M$. Define $w(\delta)$ as the number of these $s$ primes that do not divide $\delta$, and let
--   $$S(q)=\sum_{a<n_A,\ b<n_B,\ c<n_C}\mathbf1_{q\mid\delta}\,w(\delta).$$
--   Then
--   $$\sum_{i=0}^{s-1}S(qp_i)\le\operatorname{log}_y^{\mathbb N}(M)\,S(q),$$
--   where the integer logarithm is $\lfloor\log_y M\rfloor$ for $M\ge1$ and is zero for $M=0$.
--
--   This bounds the aggregate weighted false-triple score over all candidate prime extensions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPrimeChain.lean#L61-L91

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_PrimeChain_prime_divisors_card_le_log
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

theorem ThreeSum.LightPrimeChain.sum_scores_le_log : ∀ (primes : Nat → Nat) (s q nA nB nC : Nat) (A B C : Nat → Int) (y M : Nat)
  (hy : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
  (hprime : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i))
  (hinj :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i s →
        ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j)
  (hlo : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → @LE.le.{0} Nat instLENat y (primes i))
  (hbound :
    ∀ (t : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)),
      @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
          (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
            (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
          (ThreeSum.ModuloCounts.triples nA nB nC) t →
        @LE.le.{0} Nat instLENat (ThreeSum.ModuloCounts.difference A B C t).natAbs M),
  @LE.le.{0} Nat instLENat
    (∑ i ∈ Finset.range s,
      ThreeSum.WeightedScore.score primes s
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (primes i)) nA nB nC A B C)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.log y M)
      (ThreeSum.WeightedScore.score primes s q nA nB nC A B C)) := by
  sorry
