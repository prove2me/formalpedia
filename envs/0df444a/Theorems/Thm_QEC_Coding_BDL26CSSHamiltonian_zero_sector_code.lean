-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zero_sector_code
-- name    : QEC.Coding.BDL26CSSHamiltonian.zero_sector_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:03:18.723003+00:00
-- url     : https://prove2.me/theorems/fc87d414-af11-4a84-8c70-e73cb0934b9f
-- title:
--   BDL26 CSSHamiltonian: zero sector code
-- statement:
--   The BDL26 CSSHamiltonian construction uses the zero sector code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L27-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L27-L29

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25

theorem QEC.Coding.BDL26CSSHamiltonian.zero_sector_code : sector S n 0 = (complex S n).binaryCSSCode.stabilizer.code.carrier := by sorry
