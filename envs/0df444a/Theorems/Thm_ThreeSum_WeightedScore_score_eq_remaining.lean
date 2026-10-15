-- Prove2me | Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining
-- name    : ThreeSum.WeightedScore.score_eq_remaining
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:37:16.702869+00:00
-- url     : https://prove2.me/theorems/5dae0a3a-ec7e-46f1-a8b0-ee51de470a54
-- title:
--   The weighted modular score equals the final correction remainder
-- statement:
--   Let $a,b,c:\mathbb N\to\mathbb Z$ have specified lengths $n_A,n_B,n_C$, and let $p_0,\ldots,p_{s-1}$ be pairwise distinct natural primes. Let $N_m$ count index triples in these lengths for which $m\mid c_k-b_j-a_i$. Define $J(q,p)=q$ if $p\mid q$, and $J(q,p)=qp$ otherwise. The weighted score counts each triple divisible by $q$ with weight equal to the number of auxiliary primes that do not divide its difference. For any $q\in\mathbb N$,
--
--   $$
--   \operatorname{score}=sN_q-\sum_{j=0}^{s-1}N_{J(q,p_j)}
--   =\operatorname{remaining}(s).
--   $$
--
--   Subtraction is the natural-number subtraction of the defined correction accumulator. This matches the score specification with the array-ordered correction computation, including shared factors with $q$.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightedScore.lean#L108-L132

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
import Theorems.Thm_ThreeSum_Arithmetic_mul_dvd_iff_of_bezout


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli

theorem ThreeSum.WeightedScore.score_eq_remaining : ∀ (primes : Nat → Nat) (s q nA nB nC : Nat) (a b c : Nat → Int)
  (hprime : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i))
  (hinj :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i s →
        ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j),
  @Eq.{1} Nat (ThreeSum.WeightedScore.score primes s q nA nB nC a b c)
    (ThreeSum.WeightedScore.remaining primes s q nA nB nC a b c s) := by
  sorry
