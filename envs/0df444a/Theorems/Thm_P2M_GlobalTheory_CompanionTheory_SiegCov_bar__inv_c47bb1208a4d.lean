-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegCov_bar__inv_c47bb1208a4d
-- name    : P2M_GlobalTheory_CompanionTheory_SiegCov_bar__inv_c47bb1208a4d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:21.60485+00:00
-- url     : https://prove2.me/theorems/967106c2-3459-4129-b62f-48b1a6770ce6
-- title:
--   P2 M Global Theory Companion Theory Sieg Cov bar  inv c47bb1208a4d: P2 M Global Theory Companion Theory Sieg Cov bar  inv c47bb1208a4d
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Cov bar  inv c47bb1208a4d construction uses the P2 M Global Theory Companion Theory Sieg Cov bar  inv c47bb1208a4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L84-L87

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegCov
variable {R : Type} [CommRing R]

theorem P2M_GlobalTheory_CompanionTheory_SiegCov_bar__inv_c47bb1208a4d (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegCov».«barσ_inv» := P2M_GlobalTheory_CompanionTheory_SiegCov_bar__inv_c47bb1208a4d
