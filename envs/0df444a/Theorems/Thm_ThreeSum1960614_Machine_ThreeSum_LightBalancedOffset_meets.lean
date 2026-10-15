-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBalancedOffset_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:08.393851+00:00
-- url     : https://prove2.me/theorems/8f391c8d-4645-429f-ab50-beda84bbf0e7
-- title:
--   Execution of the least balanced cyclic offset
-- statement:
--   Let $p>0$, $p\le2^k$, and $F,H:\mathbb Z/p\mathbb Z\to\mathbb N$ have coefficients bounded by $U$. Suppose memory $\mu$ stores their length-$2^k$ padded vectors, with the H vector reversed by negation of the residue. Let $\lambda,P,d$ be limits, program and depth, and suppose the balanced-offset, cyclic-product, least-minimum and concrete Karatsuba procedures occur through their literal closure records. Both inputs, the length-$2^{k+1}$ product and length-$p$ correlation output end before scratch $w$; product and correlation outputs are disjoint; $w+8\cdot2^k$ fits memory; addresses fit words; the Karatsuba word bound fits; and $d+k+3$ is allowed. Then the call returns
--
--   $$\min\operatorname*{arg\,min}_{0\le r<p}\operatorname{correlation}(F,H,r),$$
--
--   within its stated time, preserving every cell below $w$ outside the product and correlation outputs.
--
--   This executes the deterministic balanced common-offset choice through fast convolution and exact tie breaking.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBalancedOffset.lean#L45-L77

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCyclic_correlation_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMinimum_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightBalancedOffset
end ThreeSum.LightBalancedOffset
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
end ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBalancedOffset
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Finset
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.meets {pMain pCyclic pMinimum pMultiply pHalf pLinear pFill : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.body pCyclic pMinimum))
    (hcyclic : P[pCyclic]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear))
    (hminimum : P[pMinimum]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body)
    (K : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p F)))
    (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))))
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p F) (U : ℤ))
    (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z))) (U : ℤ))
    (haf : a+2^k ≤ work) (hbf : b+2^k ≤ work)
    (hpf : prod+2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : _root_.Light.Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [2^k,a,b,prod,dst,work,p] μ (_root_.ThreeSum.LightBalancedOffset.time k p)
      fun r μ' => r = (_root_.ThreeSum.LightBalancedOffset.offset F H : ℤ) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by sorry
