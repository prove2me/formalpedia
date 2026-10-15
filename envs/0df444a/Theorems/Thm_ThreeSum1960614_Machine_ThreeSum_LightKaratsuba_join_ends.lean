-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_join_ends
-- name    : ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:44.831285+00:00
-- url     : https://prove2.me/theorems/33672173-db4c-461a-8e2a-64aa5cfb31e7
-- title:
--   Executing Karatsuba recombination into the product array
-- statement:
--   Let $n=2h>0$ and let three consecutive length-$n$ workspace arrays have absolute values at most $U$. Suppose the $2n$ output cells precede workspace, the full workspace fits, $10U$ and addresses fit words, and linear/fill helpers and a call level are available. The join block writes each defined Karatsuba recombination coefficient, preserving all other protected cells and meeting the join-time bound.
--
--   This block contract writes the recombined product coefficients used by the verified cyclic-correlation implementation.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightKaratsuba.lean#L143-L272

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets

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

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends (hLinear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    (hFill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ}
    (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧
      |μ (work + 2 * n + i)| ≤ U)
    (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joinBody pLinear pFill)
      ⟨_root_.Light.frame [n, a, b, out, work, half, r], μ⟩ (_root_.ThreeSum.LightKaratsuba.joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = _root_.ThreeSum.LightKaratsuba.joined μ work n half j) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ σ'.mem work out (2 * n) := by sorry
