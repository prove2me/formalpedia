-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:03.994822+00:00
-- url     : https://prove2.me/theorems/2f62c9fb-3a54-4588-beed-1d9256a747ca
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T add  abfcc11f156d: P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T add  abfcc11f156d
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T add  abfcc11f156d construction uses the P2 M Global Theory Companion Theory Sieg Loc Herm Orth c T add  abfcc11f156d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L22-L25

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

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«HermOrth».«cT_add'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d
