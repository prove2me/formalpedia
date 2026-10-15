-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorBands_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:45:57.30685+00:00
-- url     : https://prove2.me/theorems/b64b87cd-b2c1-45cf-9a64-10906ae8baa6
-- title:
--   Execution of original-input color classes and normalized bands
-- statement:
--   Let $n\le2^W$, band size $g>0$, input $x:\operatorname{Fin}(n)\to\mathbb Z$ with $|x_i|\le U$, and coloring parameter $p$ of width $W$ be given. Suppose memory stores the original list, followed in order by its color row, three length-$n+1$ class buffers, three normalized value arrays and their length-$2+2n$ band headers, then scratch. Assume every preceding reservation ends before the next, addresses fit words, the exact color-band space/word budgets fit and $d$ plus its stated depth requirement is allowed. A literal procedure-closure record identifies all callees. The program normalizes the color-0 and color-1 values and negated color-2 values, constructs their exact band tables and owner enumeration, meets its stated time and preserves cells below the color row.
--
--   This connects the original signed input and index coloring to the three normalized lists used by the complete solver.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightColorBands.lean#L55-L127

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_time_bound

namespace ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs
end ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs
namespace ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs
end ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs.meets {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.Procs P pMain) (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : _root_.ThreeSum.LightColorBands.space work W n g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightColorBands.word W n g U : ℤ) ≤ lim.word) (hd : d+_root_.ThreeSum.LightColorBands.depth W n g ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (_root_.ThreeSum.LightColorBands.time W n g)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (_root_.ThreeSum.ColorClassLists.classList p x 0 1) (_root_.ThreeSum.ColorClassLists.classList p x 1 1) (_root_.ThreeSum.ColorClassLists.classList p x 2 (-1)) r ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ ν colors) := by sorry
