-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_count_ends
-- name    : ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:17:25.110699+00:00
-- url     : https://prove2.me/theorems/a37c48a1-7bdc-4ad8-bfff-33d3892f9c69
-- title:
--   Histogram counting from a zeroed destination
-- statement:
--   Let $\lambda,P,d$ be run limits, program and depth; $\ell$ a local-variable map; $\mu$ memory; and $s,b,n,p\in\mathbb N$ source, destination, item count and residue count. Assume the first three locals hold $s,b,n$; addresses fit words; both arrays fit memory and are disjoint; source entry $i<n$ holds a natural code $c_i<p$; and every destination cell starts at zero. The counting statement ends within its specified $n$-dependent time with
--
--   $$\mu'(b+r)=|\{i<n:c_i=r\}|\qquad(r<p),$$
--
--   preserving every cell outside the histogram.
--
--   This establishes exact multiplicity counting for physical input and hash-code arrays.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightHistogram.lean#L45-L96

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ} {src dst n p : ℕ}
    (key : ℕ → ℕ) (hsrc : loc 0 = src) (hdst : loc 1 = dst) (hlen : loc 2 = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst + r) = 0) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.countBody ⟨loc, μ⟩ (_root_.ThreeSum.LightHistogram.countTime n) fun σ' =>
      (∀ r < p, σ'.mem (dst + r) = _root_.ThreeSum.LightHistogram.count key r n) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ σ'.mem dst p := by sorry
