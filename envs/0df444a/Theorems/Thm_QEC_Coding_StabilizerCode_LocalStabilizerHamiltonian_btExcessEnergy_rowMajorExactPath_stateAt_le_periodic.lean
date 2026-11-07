-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_rowMajorExactPath_stateAt_le_periodic
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_rowMajorExactPath_stateAt_le_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:18:19.301855+00:00
-- url     : https://prove2.me/theorems/30677905-0024-44a8-be31-c40378cd1053
-- title:
--   Local Stabilizer Hamiltonian: bt Excess Energy row Major Exact Path state At le periodic
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the bt Excess Energy row Major Exact Path state At le periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L992-L1029
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L992-L1029

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_rowMajorExactPath_stateAt_le_periodic
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L) (hStripWidth : stripWidth ≤ r)
    (hRowLocal :
      StripGeometry.HasPeriodicRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth)
    (hn : n ≤ (StripGeometry.rowMajorExactPath Q).increments.length) :
    H.btExcessEnergy ((StripGeometry.rowMajorExactPath Q).stateAt n) ≤
      4 * r * r * H.participationBound := by sorry
