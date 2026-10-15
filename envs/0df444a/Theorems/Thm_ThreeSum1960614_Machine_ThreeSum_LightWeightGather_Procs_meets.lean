-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightGather_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightWeightGather.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:11.280428+00:00
-- url     : https://prove2.me/theorems/d2306fc3-1b84-47b3-8377-3de218029c6c
-- title:
--   Gathering selected coefficient rows
-- statement:
--   Let a row-major source have $N$ rows of width $W$, and let a stored selection array choose $R$ valid row indices. Under the concrete copy/wrapper interface, input-before-output ordering, output-space, word, address, and call-depth bounds, the procedure writes $$\nu(\mathrm{dst}+iW+a)=\mu(\mathrm{src}+\mathrm{select}(i)W+a)$$ for $i<R,a<W$. It meets its prescribed gathering time and changes no cells outside the output.
--
--   Retains repeated selected candidates in exact schedule order. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightGather.lean#L39-L105

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightWeightGather
end ThreeSum.LightWeightGather
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightGather
end ThreeSum1960614.Machine.ThreeSum.LightWeightGather

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWeightGather
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightGather

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1000000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightWeightGather.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightGather.Procs P pMain)
    {μ : ℕ → ℤ} {indices src dst N rows width : ℕ} (select : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hindices : indices+rows ≤ dst) (hsrc : src+N*width ≤ dst)
    (hspace : dst+rows*width ≤ lim.space)
    (hword : (_root_.ThreeSum.LightWeightGather.word N rows width : ℤ) ≤ lim.word)
    (hselect : ∀ i < rows, select i < N)
    (hread : ∀ i < rows, μ (indices+i) = (select i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [indices,src,dst,rows,width] μ (_root_.ThreeSum.LightWeightGather.time rows width)
      (fun _ μ' =>
        (∀ i < rows, ∀ a < width, μ' (dst+i*width+a) = μ (src+select i*width+a)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (rows*width)) := by sorry
