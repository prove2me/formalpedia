-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_projector_range_finrank_two
-- name    : QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_finrank_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:38:16.669435+00:00
-- url     : https://prove2.me/theorems/c8b1d3e6-26aa-4803-98ae-2b7c8b7fd398
-- title:
--   BDL26 CSSHamiltonian: zero projector range finrank two
-- statement:
--   The BDL26 CSSHamiltonian construction uses the zero projector range finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L95-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L95-L98

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

theorem QEC.Coding.BDL26CSSHamiltonian.zero_projector_range_finrank_two :
    Module.finrank ℂ (LinearMap.range (projector S n 0)) = 2 := by sorry
