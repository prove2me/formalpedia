-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_neg__c113ada7890a
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_neg__c113ada7890a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:48.034715+00:00
-- url     : https://prove2.me/theorems/0d5088db-6f83-442d-9b9e-9b7c56f58ef5
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T neg  c113ada7890a: P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T neg  c113ada7890a
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T neg  c113ada7890a construction uses the P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T neg  c113ada7890a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L27-L30

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

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_neg__c113ada7890a (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (-x) = -cT σ x := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«HermOrth».«cT_neg'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_neg__c113ada7890a
