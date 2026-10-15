-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWanted_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:02:47.975864+00:00
-- url     : https://prove2.me/theorems/64a8310d-b4f0-4aa3-ba44-bdde57e466a9
-- title:
--   Execution of one complete guarded wanted reporter
-- statement:
--   Let finite decidable index types carry finite sets A,B,C and integer maps $a,b,c$. Fix arithmetic modulus $p\in\mathbb N$, shift $\delta\in\mathbb Z$, block parameters $h,J$, terminal depth $K\le J$ and wanted label $w$ satisfying A membership and its lifted-key congruence. Let $I$ be the original raw-incidence set, $m_0$ its root mass at $w$, and let old cumulative mass $m$ and threshold $\tau$ be stored in the two counter cells. Suppose memory stores both exact source transforms, every catalog through $K$ with its exact metadata and query scratch bounds, original output masks and occurrence row, cover data, original B/C arrays and their correct residue buckets. All retained data, counter, packed rows and frontier slots satisfy the stated ordered bounds before child and terminal scratch. Require the explicit child/query/terminal capacities and work bounds; all address, signed-value, original target-sum and pair-count bounds; the guard sum $m+m_0+\tau+2$ fitting a word; and depth sufficient for $K$, twice global width, terminal frontier length, terminal candidate count and twenty-seven overhead calls.
--
--   The fixed reporter packs the query, initializes the frontier, applies the cumulative guard and, if needed, traverses to depth $K$ and tests original values. It returns
--
--   $$r\in\{0,1\},\qquad r=1\iff \tau<m+m_0\ \lor\ \exists u\in\operatorname{frontier}(I,w,K):\operatorname{TerminalHit}(u).$$
--
--   It sets the cumulative counter to $m+m_0$, meets its specified actual execution budget and preserves all cells below the packed-row base except that counter.
--
--   This is the full executed wanted-label contract connecting early dense stopping and exact terminal reporting.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingWanted.lean#L49-L209

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
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
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitializeSeparated
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedSearch
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedSearch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightReportingWanted
end ThreeSum.LightReportingWanted
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWanted
end ThreeSum1960614.Machine.ThreeSum.LightReportingWanted
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
set_option maxHeartbeats 5000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program_meets {μ : ℕ→ℤ}
    {h J K srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR root catalogs rawRows rows cover counter
      baseL baseR masks childL childR counts selected maskBase work terminalMasks masksL masksR base bitBase rowOut old threshold d : ℕ}
    (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (D : ℕ→_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hK : K≤J)
    (hkey : w.1∈A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a w.1%(p : ℤ)+_root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ (p : ℤ) shift B C b c w.2.2 baseL baseR)
    (HC : ∀ (j : ℕ) (hj : j≤K), _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ (D j) (hj.trans hK) (p : ℤ) shift B C b c w.2.2)
    (HB : ∀ j≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J j (D j) baseL baseR counter)
    (HW : ∀ j≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J j (D j) B.card C.card maskBase work)
    (hmeta : ∀ j≤K, _root_.ThreeSum1960614.Machine.Light.SegN μ (catalogs+5*j) ((D j).record h j))
    (hmetaEnd : catalogs+5*(K+1)≤counter)
    (hraw : rawRows+J≤rows) (hrows : rows+J≤root) (hcounter : counter+2≤rawRows)
    (hgroup : μ (cover+3)=(_root_.ThreeSum.LocalCoverBounds.groupSize h : ℤ)) (hcoverEnd : cover+4≤counter)
    (hreadRaw : _root_.ThreeSum1960614.Machine.Light.SegN μ rawRows (_root_.ThreeSum.BlockMaskLayout.rawMasks (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)))
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hguardWord : ((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hout : _root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤ masks)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childL) (hchildL : childL+_root_.ThreeSum.LocalCoverBounds.groupSize h≤childR)
    (hchildR : childR+_root_.ThreeSum.LocalCoverBounds.groupSize h≤counts) (hcounts : counts+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ selected)
    (hselected : selected+_root_.ThreeSum.LocalCoverBounds.groupSize h≤ maskBase)
    (hparams : J+464*h+_root_.ThreeSum.LocalCoverBounds.groupSize h+_root_.ThreeSum.LightBlockQuery.sourceCut h J≤lim.space)
    (hpackSpace : work+(464*h+1)≤lim.space)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (left i)) NL (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) offsetsL flatL)
    (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (right i)) NR (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) offsetsR flatR)
    (hsrcL : srcL+NL≤counter) (hsrcR : srcR+NR≤counter)
    (hoffsetsL : offsetsL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤counter) (hoffsetsR : offsetsR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J+1≤counter)
    (hflatL : flatL+NL≤counter) (hflatR : flatR+NR≤counter)
    (hocc : occ+J≤rows) (hoccApart : _root_.Light.Apart counter 1 occ J)
    (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤counter)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤counter)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤counter)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤counter)
    (hterminalSlot : _root_.ThreeSum.ReportingHostFrontierLayout.slot root (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w) (K+1)≤terminalMasks)
    (hterminalMasks : terminalMasks+_root_.ThreeSum.LightReportingTerminalMasks.count h J K≤ masksL) (hmasksL : masksL+_root_.ThreeSum.LightReportingTerminalMasks.count h J K≤ masksR)
    (hmasksR : masksR+_root_.ThreeSum.LightReportingTerminalMasks.count h J K≤base)
    (hstop : _root_.ThreeSum.LightReportingTerminalPreparation.stop base (J*(464*h)) (_root_.ThreeSum.LightReportingTerminalMasks.count h J K)≤bitBase)
    (hbits : bitBase+J*(464*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.space work h J≤lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences w.2.2) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |a w.1|≤lim.word) (htarget : ∀ i<NL, |a w.1+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word)
    (hd : d+K+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w K).length+
      _root_.ThreeSum.LightReportingTerminalMasks.count h J K+27≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program 137 d
      [a w.1,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,
        occ,maps,candidates,histL,histR,K,root,catalogs,rows,baseL,baseR,masks,childL,childR,counts,selected,
        maskBase,work,0,_root_.ThreeSum.LightBlockQuery.sourceCut h J,terminalMasks,masksL,masksR,base,bitBase,rowOut,rawRows,cover,counter]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift left right NL NR old threshold (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w D K)
      (fun r ν =>
        let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
        (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w ∨
          ∃ pre∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w K,
            _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 K pre) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν rows counter 1) := by sorry
