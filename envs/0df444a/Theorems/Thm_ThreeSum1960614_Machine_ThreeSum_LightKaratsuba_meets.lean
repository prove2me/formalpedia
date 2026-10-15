-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:59.779185+00:00
-- url     : https://prove2.me/theorems/fc3c0408-d2dc-4f54-a1c4-22e88bf999be
-- title:
--   Execution of coefficient-array Karatsuba multiplication
-- statement:
--   Let $k,U\in\mathbb N$, $n=2^k$, and integer coefficient lists $A,B$ each have length $n$ and absolute coefficient bounds $U$. Suppose memory $\mu$ stores them at their source bases. Let a literal closure record identify the recursive Karatsuba, halving, linear-combination and fill bodies in program $P$. Assume addresses fit words; both sources and the length-$2n$ output end before scratch $w$; $w+8n$ fits memory; and the explicit multiplication word bound fits. At every depth $d$ with $d+k+1$ allowed, the call writes the exact length-$2n$ product coefficients within its prescribed recursive time, preserving cells below $w$ outside that output.
--
--   This supplies actual fast polynomial multiplication for modular counting and correlation.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightKaratsuba.lean#L579-L642

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_recurse_ends

namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill)
    (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as (U : ℤ)) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2 ^ k) U : ℤ) ≤ lim.word) :
    ∀ d, d + k + 1 ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSelf d [2 ^ k, a, b, out, work] μ (_root_.ThreeSum.LightKaratsuba.time k)
        (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ out (2 ^ k) work as bs μ') := by sorry
