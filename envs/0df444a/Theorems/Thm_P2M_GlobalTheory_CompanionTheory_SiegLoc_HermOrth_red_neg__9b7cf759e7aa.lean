-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:23.41428+00:00
-- url     : https://prove2.me/theorems/7c99d98b-cb87-4f63-92db-e6fe084ecd18
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Herm Orth red neg  9b7cf759e7aa: P2 M Global Theory Companion Theory Sieg Loc Herm Orth red neg  9b7cf759e7aa
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Herm Orth red neg  9b7cf759e7aa construction uses the P2 M Global Theory Companion Theory Sieg Loc Herm Orth red neg  9b7cf759e7aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L17-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«HermOrth».«red_neg'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_red_neg__9b7cf759e7aa
