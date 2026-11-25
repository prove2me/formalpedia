-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocFlat_ch_add__d386fdda424f
-- name    : P2M_GlobalTheory_LocFlat_ch_add__d386fdda424f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:28.938108+00:00
-- url     : https://prove2.me/theorems/e03c1e5c-cab1-431a-acca-9c1280835caf
-- title:
--   P2 M Global Theory Loc Flat ch add  d386fdda424f: P2 M Global Theory Loc Flat ch add  d386fdda424f
-- statement:
--   The P2 M Global Theory Loc Flat ch add  d386fdda424f construction uses the P2 M Global Theory Loc Flat ch add  d386fdda424f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapsPreserveSchwartzBruhatAndSurjective.lean#L36-L37

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

theorem P2M_GlobalTheory_LocFlat_ch_add__d386fdda424f (a b : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (a + b) = ch a + ch b := by sorry

alias «GlobalTheory».«LocFlat».«ch_add'» := P2M_GlobalTheory_LocFlat_ch_add__d386fdda424f
