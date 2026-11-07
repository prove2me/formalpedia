-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_boundedDiameter
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_boundedDiameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:34.381794+00:00
-- url     : https://prove2.me/theorems/8aa90fd0-49e4-44d9-a59a-ffca74fa6727
-- title:
--   Local Stabilizer Hamiltonian: generator Support bounded Diameter
-- statement:
--   The recorded locality bound applies to the actual selected-term support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L97-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L97-L101

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_boundedDiameter
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Locality.BoundedDiameter H.geometry (H.generatorSupport j : Set ι)
      H.interactionRange := by sorry
