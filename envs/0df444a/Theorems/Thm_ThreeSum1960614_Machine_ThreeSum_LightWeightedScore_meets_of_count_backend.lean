-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedScore_meets_of_count_backend
-- name    : ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.meets_of_count_backend
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:43:06.707031+00:00
-- url     : https://prove2.me/theorems/bbbc1b41-c419-459b-8cdc-1d9ed1710a09
-- title:
--   Weighted scoring from a verified counting backend
-- statement:
--   Let three stored source arrays have lengths at most $N$, and let a stored auxiliary array contain distinct primes $\ell_i$. Suppose $0<q\le M$, every $q\ell_i\le M$, input arrays precede scratch, the stated logarithmic scratch, word, address, and depth bounds hold, and a counting backend correctly counts modular triples for every positive modulus at most $M$ while preserving the input prefix. The concrete weighted-score wrapper returns the exact defined score in its specified time and preserves the prefix.
--
--   Connects the executable aggregate score to its modular-counting specification. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightedScore.lean#L104-L209

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean
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
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Choose.Bounds
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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
import Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightWeightedScore
end ThreeSum.LightWeightedScore
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
end ThreeSum1960614.Machine.ThreeSum.LightWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.WeightedModuli
end ThreeSum1960614.Machine.ThreeSum.WeightedModuli
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedModuli
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedModuli
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.meets_of_count_backend {pMain pCount pJoint pEmod : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.body pCount pJoint))
    (hjoint : P[pJoint]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.jointBody pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod countTime : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free) (hN : N ≤ lim.space)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word)
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod)
    (hcount : ∀ (ν : ℕ → ℤ) (p : ℕ), _root_.ThreeSum1960614.Machine.Light.Kept μ ν free → 0 < p → p ≤ maxMod →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pCount (d+1) [a,b,c,nA,nB,nC,p,N,free] ν countTime
        (fun r ν' => r = (_root_.ThreeSum.ModuloCounts.count p nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept ν ν' free)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ (_root_.ThreeSum.LightWeightedScore.time countTime s maxMod)
      fun r μ' => r = (_root_.ThreeSum.WeightedScore.score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free := by sorry
