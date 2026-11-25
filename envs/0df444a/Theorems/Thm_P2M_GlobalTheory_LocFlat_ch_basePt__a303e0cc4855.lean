-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_ch_basePt__a303e0cc4855
-- name    : P2M_GlobalTheory_LocFlat_ch_basePt__a303e0cc4855
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:27.61681+00:00
-- url     : https://prove2.me/theorems/bf32c836-8ed8-43ad-9234-977e99e50ef2
-- title:
--   P2 M Global Theory Loc Flat ch base Pt  a303e0cc4855: P2 M Global Theory Loc Flat ch base Pt  a303e0cc4855
-- statement:
--   The P2 M Global Theory Loc Flat ch base Pt  a303e0cc4855 construction uses the P2 M Global Theory Loc Flat ch base Pt  a303e0cc4855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L39-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem P2M_GlobalTheory_LocFlat_ch_basePt__a303e0cc4855 (x₀ : Matrix n n' k) : ch (basePt c x₀) = 0 := by sorry

alias «GlobalTheory».«LocFlat».«ch_basePt'» := P2M_GlobalTheory_LocFlat_ch_basePt__a303e0cc4855
