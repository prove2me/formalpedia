-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_zError_syndrome
-- name    : QEC.Coding.BDL26CSSHamiltonian.zError_syndrome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:56:01.760965+00:00
-- url     : https://prove2.me/theorems/c14b993b-c7d0-474a-b1d2-2a848e5c8cac
-- title:
--   BDL26 CSSHamiltonian: z Error syndrome
-- statement:
--   Z errors have X-row syndromes, on the literal transposed presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L81-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L81-L84

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

theorem QEC.Coding.BDL26CSSHamiltonian.zError_syndrome (e : Word (ZMod 2) (Physical S n)) : xSyndrome S n e =
    BDL26RZMap1CoordinateBridge.tannerCoboundary1
      (BDL26FiniteTannerSquare.transposePresentation (presentation S n)) e := by sorry
