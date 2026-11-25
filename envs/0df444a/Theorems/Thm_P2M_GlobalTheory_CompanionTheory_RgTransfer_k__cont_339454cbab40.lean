-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40
-- name    : P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:03.600408+00:00
-- url     : https://prove2.me/theorems/6199375f-fe9e-4a20-8768-b7f1a1e9ad5c
-- title:
--   P2 M Global Theory Companion Theory Rg Transfer k  cont 339454cbab40: P2 M Global Theory Companion Theory Rg Transfer k  cont 339454cbab40
-- statement:
--   The P2 M Global Theory Companion Theory Rg Transfer k  cont 339454cbab40 construction uses the P2 M Global Theory Companion Theory Rg Transfer k  cont 339454cbab40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L94-L95

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}

theorem P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40 (hL : IsLevi Γ K Q Γ' K' π ι c₀) : Continuous (kι hL) := by sorry

alias «GlobalTheory».«CompanionTheory».«RgTransfer».«kι_cont» := P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40
