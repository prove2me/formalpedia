-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHeaderBands_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:43:19.416985+00:00
-- url     : https://prove2.me/theorems/a82e0b6b-56fc-4853-91b0-e139ac235250
-- title:
--   Band candidate tables from retained endpoint headers
-- statement:
--   Let three interval families be stored in actual headers for source lengths $n_A,n_B,n_C$, with endpoints bounded by $U$. Suppose all headers precede the destination and the concrete procedure interface and specified enumeration space, word, address, and depth bounds hold. The routine returns the exact three-rectangle cell count, constructs all prescribed band lookup tables in its stated time, and preserves the input prefix.
--
--   Constructs the owner-candidate tables from actual retained input headers. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightHeaderBands.lean#L39-L64

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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

namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Procs


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightHeaderBands
end ThreeSum.LightHeaderBands
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightHeaderBands
end ThreeSum1960614.Machine.ThreeSum.LightHeaderBands

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightHeaderBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets {pMain a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ a nA A) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ b nB B) (hC : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ c nC C)
    (hAU : _root_.ThreeSum.LightBandEnumeration.Bounded A U) (hBU : _root_.ThreeSum.LightBandEnumeration.Bounded B U)
    (hCU : _root_.ThreeSum.LightBandEnumeration.Bounded C U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,dst] μ (_root_.ThreeSum.LightHeaderBands.time A.size B.size C.size)
      (fun r μ' => r = (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ' dst A B C ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' dst) := by sorry
