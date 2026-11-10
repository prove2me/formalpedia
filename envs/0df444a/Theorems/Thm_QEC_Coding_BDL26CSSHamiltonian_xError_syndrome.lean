-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_xError_syndrome
-- name    : QEC.Coding.BDL26CSSHamiltonian.xError_syndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:53:42.672801+00:00
-- url     : https://prove2.me/theorems/d4b13880-21df-4780-be4d-339f8812db67
-- title:
--   BDL26 CSSHamiltonian: x Error syndrome
-- statement:
--   X errors have Z-row syndromes, on the actual degree-two coboundary image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L77-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L77-L78

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

theorem QEC.Coding.BDL26CSSHamiltonian.xError_syndrome (e : Word (ZMod 2) (Physical S n)) : zSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1 (presentation S n) e := by sorry
