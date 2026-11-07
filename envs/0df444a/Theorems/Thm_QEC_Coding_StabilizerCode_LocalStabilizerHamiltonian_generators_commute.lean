-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generators_commute
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generators_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:50:29.136234+00:00
-- url     : https://prove2.me/theorems/e8950b30-f11e-44ac-863c-e4f721f8bf26
-- title:
--   Local Stabilizer Hamiltonian: generators commute
-- statement:
--   The selected binary generators commute because they lie in the same stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L76-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L76-L80

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generators_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commutes (H.generators j) (H.generators k) := by sorry
