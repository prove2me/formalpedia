-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_chain_css_carrier_finrank_two
-- name    : QEC.Coding.BDL26CSSHamiltonian.chain_css_carrier_finrank_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:31:35.119726+00:00
-- url     : https://prove2.me/theorems/e1b4db60-59ad-4395-9399-819e514deae4
-- title:
--   BDL26 CSSHamiltonian: chain css carrier finrank two
-- statement:
--   The actual binary CSS code lives on the existing physical QubitRegister.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L34-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L34-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSHamiltonian.chain_css_carrier_finrank_two :
    Module.finrank ℂ (complex S n).binaryCSSCode.stabilizer.code.carrier = 2 := by sorry
