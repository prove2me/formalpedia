-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6
-- name    : P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:37.700993+00:00
-- url     : https://prove2.me/theorems/fbd74417-5e01-487d-a93b-e26fa0d0b37a
-- title:
--   P2 M Global Theory Companion Theory Sieg Loc Herm Orth trace single mul  b40bc346e0d6: P2 M Global Theory Companion Theory Sieg Loc Herm Orth trace single mul  b40bc346e0d6
-- statement:
--   The P2 M Global Theory Companion Theory Sieg Loc Herm Orth trace single mul  b40bc346e0d6 construction uses the P2 M Global Theory Companion Theory Sieg Loc Herm Orth trace single mul  b40bc346e0d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L36-L38

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

theorem P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6 {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegLoc».«HermOrth».«trace_single_mul'» := P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6
