-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_mul__06396bb29280
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_mul__06396bb29280
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:47.707202+00:00
-- url     : https://prove2.me/theorems/4cadeb4f-b210-4a15-8b0d-c73d430c6c85
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Nu Diag red mul  06396bb29280: P2 M Global Theory Companion Theory Sieg Loc Nu Diag red mul  06396bb29280
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Nu Diag red mul  06396bb29280 construction uses the P2 M Global Theory Companion Theory Sieg Loc Nu Diag red mul  06396bb29280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L38-L40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.NuDiag

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_mul__06396bb29280 {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    red ϖ k (a * b) = red ϖ k a * red ϖ k b := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«NuDiag».«red_mul'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_mul__06396bb29280
