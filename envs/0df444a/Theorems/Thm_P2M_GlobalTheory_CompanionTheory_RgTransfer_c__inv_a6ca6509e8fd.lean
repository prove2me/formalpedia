-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgTransfer_c__inv_a6ca6509e8fd
-- name    : P2M_GlobalTheory_CompanionTheory_RgTransfer_c__inv_a6ca6509e8fd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:51.623072+00:00
-- url     : https://prove2.me/theorems/18fdb787-f231-4d2e-931b-0e73fed9a713
-- title:
--   P2 M Global Theory Companion Theory Rg Transfer c  inv a6ca6509e8fd: P2 M Global Theory Companion Theory Rg Transfer c  inv a6ca6509e8fd
-- statement:
--   The P2 M Global Theory Companion Theory Rg Transfer c  inv a6ca6509e8fd construction uses the P2 M Global Theory Companion Theory Rg Transfer c  inv a6ca6509e8fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean#L38-L43

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

theorem P2M_GlobalTheory_CompanionTheory_RgTransfer_c__inv_a6ca6509e8fd (hL : IsLevi Γ K Q Γ' K' π ι c₀) (a : Q) : c₀ ((a⁻¹ : Q) : G) = (c₀ a)⁻¹ := by sorry

alias «GlobalTheory».«CompanionTheory».«RgTransfer».«c₀_inv» := P2M_GlobalTheory_CompanionTheory_RgTransfer_c__inv_a6ca6509e8fd
