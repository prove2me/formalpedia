-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_not_commutes_complement_of_not_commutes_restriction
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.not_commutes_complement_of_not_commutes_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:16:13.691198+00:00
-- url     : https://prove2.me/theorems/0488ac9b-437e-4695-a000-7f69158a4396
-- title:
--   Local Stabilizer Hamiltonian: not commutes complement of not commutes restriction
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the not commutes complement of not commutes restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L675-L693
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean#L675-L693

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.not_commutes_complement_of_not_commutes_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (Q E F : Binary ι) (j : κ)
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hdecomp : Q.vector = E.vector + F.vector)
    (hE : ¬ Commutes E (H.generators j)) :
    ¬ Commutes F (H.generators j) := by sorry
