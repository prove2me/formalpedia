-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandEnumeration_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:42:55.124198+00:00
-- url     : https://prove2.me/theorems/1abda5f7-a973-49b6-9b0a-c893a3931939
-- title:
--   Enumerating the band-owner tables from physical endpoints
-- statement:
--   Let bounded families $A,B,C$ have stored lower and upper endpoint arrays preceding destination $o$. Under the complete owner-enumeration placement, layout, space, word, and width-dependent depth requirements, the program constructs their exact owner tables, returns the prescribed table count, and preserves memory below $o$, within the finite enumeration time.
--
--   This enumeration contract supplies physical owner tables directly from bounded, stored band endpoints.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBandEnumeration.lean#L95-L257

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice

namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum.LightBandTable
end ThreeSum1960614.Machine.ThreeSum.LightBandTable


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs.meets {pMain al ah bl bh cl ch dst U d : ℕ} {μ : ℕ → ℤ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hal : al+A.size ≤ dst) (hah : ah+A.size ≤ dst)
    (hbl : bl+B.size ≤ dst) (hbh : bh+B.size ≤ dst)
    (hcl : cl+C.size ≤ dst) (hch : ch+C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+4 ≤ lim.depth)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ al ah A) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ bl bh B) (hC : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ cl ch C)
    (hAU : _root_.ThreeSum.LightBandEnumeration.Bounded A U) (hBU : _root_.ThreeSum.LightBandEnumeration.Bounded B U) (hCU : _root_.ThreeSum.LightBandEnumeration.Bounded C U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [al,ah,bl,bh,cl,ch,A.size,B.size,C.size,dst] μ
      (_root_.ThreeSum.LightBandEnumeration.time A.size B.size C.size)
      (fun r μ' => r = (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ' dst A B C ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' dst) := by sorry
