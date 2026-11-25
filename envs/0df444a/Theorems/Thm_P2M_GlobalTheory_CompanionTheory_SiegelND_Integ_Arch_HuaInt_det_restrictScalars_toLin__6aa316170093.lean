-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093
-- name    : P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:45.032136+00:00
-- url     : https://prove2.me/theorems/dedb4516-c964-426f-8576-9e8274b55324
-- title:
--   P2 M Global Theory Companion Theory Siegel ND Integ Arch Hua Int det restrict Scalars to Lin  6aa316170093: P2 M Global Theory Companion Theory Siegel ND Integ Arch Hua Int det restrict Scalars to Lin
-- statement:
--   The P2 M Global Theory Companion Theory Siegel ND Integ Arch Hua Int det restrict Scalars to Lin  6aa316170093 construction uses the P2 M Global Theory Companion Theory Siegel ND Integ Arch Hua Int det restrict Scalars to Lin  6aa316170093 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralLinearChangeVariablesComplex.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralLinearChangeVariablesComplex.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093 {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by sorry

alias «GlobalTheory».«CompanionTheory».«SiegelND».«Integ».«Arch».«HuaInt».«det_restrictScalars_toLin'» := P2M_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_det_restrictScalars_toLin__6aa316170093
