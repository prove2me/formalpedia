-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_gibbs_zError_marginal
-- name    : QEC.Coding.BDL26CSSHamiltonian.gibbs_zError_marginal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:54:46.015393+00:00
-- url     : https://prove2.me/theorems/20123c5a-b71d-4af5-99c7-623c40401e00
-- title:
--   BDL26 CSSHamiltonian: gibbs z Error marginal
-- statement:
--   The BDL26 CSSHamiltonian construction uses the gibbs z Error marginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L92-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean#L92-L96

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

theorem QEC.Coding.BDL26CSSHamiltonian.gibbs_zError_marginal (β : ℝ) (v : LinearMap.range (xSyndrome S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * CSSGibbs.qMarginalProjector (zSyndrome S n) (xSyndrome S n)
        (row_orthogonal S n) v) = (CSSGibbs.rowProbability (xSyndrome S n) (2 * β) v : ℂ) := by sorry
