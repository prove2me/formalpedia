-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_gibbs_xError_marginal
-- name    : QEC.Coding.BDL26CSSHamiltonian.gibbs_xError_marginal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:54:50.07702+00:00
-- url     : https://prove2.me/theorems/f841dff8-2381-4b46-816b-87d4a83736c5
-- title:
--   BDL26 CSSHamiltonian: gibbs x Error marginal
-- statement:
--   The BDL26 CSSHamiltonian construction uses the gibbs x Error marginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L86-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L86-L90

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

theorem QEC.Coding.BDL26CSSHamiltonian.gibbs_xError_marginal (β : ℝ) (u : LinearMap.range (zSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.pMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) u) = (CSSGibbs.rowProbability (zSyndrome S n) (2 * β) u : ℂ) := by sorry
