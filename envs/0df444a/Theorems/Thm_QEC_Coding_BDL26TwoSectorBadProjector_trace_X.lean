-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_trace_X
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.trace_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:24:06.452204+00:00
-- url     : https://prove2.me/theorems/eb2b9cd4-73e1-440b-bbf3-4563064cf5f8
-- title:
--   BDL26 Two Sector Bad Projector: trace X
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the trace X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L128-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L128-L133

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TwoSectorBadProjector
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_24
attribute [local instance] QEC.Coding.BDL26TwoSectorBadProjector._p2m_local_instance_06cc962c0b_25

theorem QEC.Coding.BDL26TwoSectorBadProjector.trace_X (β : ℝ) (BX : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * PX S n BX) = ((1 - pX S n β BX : ℝ) : ℂ) := by sorry
