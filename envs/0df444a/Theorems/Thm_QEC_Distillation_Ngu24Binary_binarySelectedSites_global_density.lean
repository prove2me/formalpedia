-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedSites_global_density
-- name    : QEC.Distillation.Ngu24Binary.binarySelectedSites_global_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:12:44.465401+00:00
-- url     : https://prove2.me/theorems/0c54ea08-5f4b-447b-a89f-df10d2f0edec
-- title:
--   Ngu24 Binary: binary Selected Sites global density
-- statement:
--   The denominator counts every qubit of one block, including unselected sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L91-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L91-L95

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]

theorem QEC.Distillation.Ngu24Binary.binarySelectedSites_global_density :
    (Fintype.card (J × Fin 512) : ℚ) / 512 ≤ (binarySelectedSites J).card := by sorry
