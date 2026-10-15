-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_recurse_ends
-- name    : ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:25.213913+00:00
-- url     : https://prove2.me/theorems/ed5b7dbb-f8b5-46ff-8291-93c997e07270
-- title:
--   The recursive Karatsuba body doubles the verified capacity
-- statement:
--   Let $m=2^k$ and let two integer coefficient lists of length $2m$ be stored and bounded by $U$. Assume the concrete Karatsuba procedure interface, input and output intervals before scratch, $16m$ scratch cells, stated word/address/depth bounds, and a recursive hypothesis correctly multiplying all admissible length-$m$ inputs one call level deeper. Then the recursive body produces the exact length-$4m$ polynomial product with its specified preservation predicate within $\operatorname{time}(k+1)-4$ steps.
--
--   Provides the recursive operational step for verified polynomial multiplication. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightKaratsuba.lean#L435-L571

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_half_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_join_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_joined_product

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

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}set_option maxHeartbeats 2000000

theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill)
    {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word)
    (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as (U : ℤ)) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work)
    (hof : out + 2 * (2 * m) ≤ work) (hspace : work + 8 * (2 * m) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih : ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
      as'.length = m → bs'.length = m → _root_.ThreeSum1960614.Machine.Light.Seg μ' a' as' → _root_.ThreeSum1960614.Machine.Light.Seg μ' b' bs' →
      _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as' (U' : ℤ) → _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs' (U' : ℤ) →
      a' + m ≤ work' → b' + m ≤ work' → out' + 2 * m ≤ work' →
      work' + 8 * m ≤ lim.space → (_root_.ThreeSum.LightKaratsuba.wordBound m U' : ℤ) ≤ lim.word →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (_root_.ThreeSum.LightKaratsuba.time k)
        (fun _ μ'' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ' out' m work' as' bs' μ'')) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurseBody pSelf pHalf pLinear pFill)
      ⟨_root_.Light.frame [2 * m, a, b, out, work], μ⟩ (_root_.ThreeSum.LightKaratsuba.time (k + 1) - 4)
      (fun σ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ out (2 * m) work as bs σ'.mem) := by sorry
