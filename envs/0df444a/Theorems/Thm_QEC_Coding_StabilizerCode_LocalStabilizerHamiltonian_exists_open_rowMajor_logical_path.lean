-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_open_rowMajor_logical_path
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_open_rowMajor_logical_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:19:30.574436+00:00
-- url     : https://prove2.me/theorems/5a74ccdc-121e-4b0a-a394-be4603bd5fb2
-- title:
--   Local Stabilizer Hamiltonian: exists open row Major logical path
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the exists open row Major logical path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L1031-L1061
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L1031-L1061

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_open_rowMajor_logical_path
    {L r stripStart stripWidth : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    ∃ γ : PauliErrorPath (ι := StripGeometry.Site L),
      γ.endpoint = Q ∧ H.HasLogicalEndpoint γ ∧
        H.pathHeight γ ≤ 2 * r * r * H.participationBound := by sorry
