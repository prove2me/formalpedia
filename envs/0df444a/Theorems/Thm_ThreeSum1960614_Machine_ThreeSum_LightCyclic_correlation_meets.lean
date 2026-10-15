-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCyclic_correlation_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:11:57.695089+00:00
-- url     : https://prove2.me/theorems/20bb451f-86c5-4be9-97db-33cb53f8265c
-- title:
--   Computing cyclic correlation through the concrete multiplier
-- statement:
--   Let $p>0$, $p\le2^k$, and let $F,H:\mathbb Z/p\mathbb Z\to\mathbb N$ have coefficient bound $U$. Suppose padded vectors for $F$ and $z\mapsto H(-z)$ are stored, the product and $p$-cell destination are disjoint, their regions precede scratch, and the Karatsuba space, word, placement, and depth bounds hold. The cyclic routine writes $\operatorname{correlation}(F,H,r)$ for every residue $r$, within its combined time, and preserves other cells below scratch.
--
--   This convolution contract computes the balancing correlation from original residue multiplicities using the concrete multiplier.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCyclic.lean#L86-L128

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_meets
import Theorems.Thm_ThreeSum_CyclicFold_cyclic_correlation

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightCyclic
end ThreeSum.LightCyclic
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
namespace ThreeSum1960614.Machine.ThreeSum.LightCyclic
end ThreeSum1960614.Machine.ThreeSum.LightCyclic
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCyclic
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets {pThis pMultiply pHalf pLinear pFill : ℕ}
    (hThis : P[pThis]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p F)))
    (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))))
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p F) (U : ℤ))
    (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : _root_.Light.Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pThis d [2^k, a, b, prod, dst, work, p] μ (_root_.ThreeSum.LightCyclic.combinedTime k p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (_root_.ThreeSum.Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by sorry
