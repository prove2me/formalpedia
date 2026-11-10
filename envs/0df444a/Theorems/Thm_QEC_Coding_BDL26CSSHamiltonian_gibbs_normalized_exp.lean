-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_gibbs_normalized_exp
-- name    : QEC.Coding.BDL26CSSHamiltonian.gibbs_normalized_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:21:42.692175+00:00
-- url     : https://prove2.me/theorems/fe0a0faf-1b45-46e8-9284-bc9d690b00b1
-- title:
--   BDL26 CSSHamiltonian: gibbs normalized exp
-- statement:
--   The BDL26 CSSHamiltonian construction uses the gibbs normalized exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L67-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L67-L69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Theorems.Thm_QEC_Coding_CSSGibbs_gibbs_normalized_exp

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_24
attribute [local instance] QEC.Coding.BDL26CSSHamiltonian._p2m_local_instance_ce658d38ff_25

theorem QEC.Coding.BDL26CSSHamiltonian.gibbs_normalized_exp (β : ℝ) : (gibbs S n β).toOperator =
    (physicalPartition S n β : ℂ)⁻¹ • thermalExponential S n β := by sorry
