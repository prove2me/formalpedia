-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:34.463794+00:00
-- url     : https://prove2.me/theorems/fabb1da5-5143-43b2-ac68-cd3f0801ea99
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Nu Diag c T mul  dbb4c9edd927: P2 M Global Theory Companion Theory Sieg Loc Nu Diag c T mul  dbb4c9edd927
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Nu Diag c T mul  dbb4c9edd927 construction uses the P2 M Global Theory Companion Theory Sieg Loc Nu Diag c T mul  dbb4c9edd927 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicityReductionDiagonalProd.lean#L30-L32

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

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927 {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«NuDiag».«cT_mul'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927
