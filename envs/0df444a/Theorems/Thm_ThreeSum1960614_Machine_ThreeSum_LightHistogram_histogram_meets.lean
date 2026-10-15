-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:27:28.862515+00:00
-- url     : https://prove2.me/theorems/1af20ef4-6963-4ddf-9301-c46e1dd0fc53
-- title:
--   Constructing the exact histogram of physical keys
-- statement:
--   Let a stored length-$n$ natural key array have every key below $p$. Suppose source and the $p$-cell destination are disjoint, both fit memory, addresses fit words, and the histogram and fill helpers and call depth are available. The program writes the exact multiplicity of each residue in its stated time, changing only the histogram cells.
--
--   This histogram contract counts physical input positions, preserving the multiplicity of equal-valued original entries.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightHistogram.lean#L103-L127

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_count_ends

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

theorem ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets {pHist pFill : ℕ}
    (hp : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill))
    (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdepth : d < lim.depth)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pHist d [(src : ℤ), dst, n, p] μ (_root_.ThreeSum.LightHistogram.histogramTime n p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = _root_.ThreeSum.LightHistogram.count key r n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p := by sorry
