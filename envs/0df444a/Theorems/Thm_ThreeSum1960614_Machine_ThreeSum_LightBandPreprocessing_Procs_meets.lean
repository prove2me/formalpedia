-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPreprocessing_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:43:12.160594+00:00
-- url     : https://prove2.me/theorems/1b38b16c-fc5c-4f7c-a06b-d2caacd09a03
-- title:
--   Normalizing three color classes and constructing band headers
-- statement:
--   Let three original integer lists be stored in consecutive protected source regions, with absolute values bounded by $U$, and let $g>0$ be the band size. Suppose the placement record installs preprocessing and its helpers; the three value arrays, endpoint headers, and scratch are ordered as specified; and the complete space, word, and depth bounds hold. The procedure produces the exact normalized-band output predicate for all three lists, returns its prescribed result, and preserves memory below the first source base within the declared preprocessing time.
--
--   This preprocessing contract constructs the normalized values and actual band endpoints required by the selected-color pipeline.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandPreprocessing.lean#L89-L221

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer

namespace ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs
end ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs
namespace ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs
end ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
end ThreeSum.LightBandPreprocessing
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
end ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandPreprocessing
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets {pMain srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : _root_.ThreeSum.LightBandPreprocessing.space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandPreprocessing.word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandPreprocessing.depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcA originalA) (hBread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcB originalB) (hCread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (_root_.ThreeSum.LightBandPreprocessing.time originalA.length originalB.length originalC.length g)
      (fun r μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcA) := by sorry
