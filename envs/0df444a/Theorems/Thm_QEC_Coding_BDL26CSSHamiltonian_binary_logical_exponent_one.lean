-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_binary_logical_exponent_one
-- name    : QEC.Coding.BDL26CSSHamiltonian.binary_logical_exponent_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:31:26.970707+00:00
-- url     : https://prove2.me/theorems/c3612289-1462-497d-a528-1c80b980b4cc
-- title:
--   BDL26 CSSHamiltonian: binary logical exponent one
-- statement:
--   Actual image ranks account for every repeated or identity labelled check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L60-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean#L60-L71

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

theorem QEC.Coding.BDL26CSSHamiltonian.binary_logical_exponent_one :
    Fintype.card (Physical S n) - CSSGibbs.checkRank (zSyndrome S n) -
      CSSGibbs.checkRank (xSyndrome S n) = 1 := by sorry
