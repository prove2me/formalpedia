-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_gibbs_commute
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.gibbs_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:31:37.171284+00:00
-- url     : https://prove2.me/theorems/3218bec2-0c01-414a-aec5-f3bd0a11a2a2
-- title:
--   BDL26 Two Sector Bad Projector: gibbs commute
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the gibbs commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L105-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L105-L107

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.gibbs_commute (β : ℝ) (A : Finset (JointImage S n)) :
    Commute (gibbs S n β).toOperator (selected S n A) := by sorry
