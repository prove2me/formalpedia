-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_joint_empty
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.joint_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:24:52.087017+00:00
-- url     : https://prove2.me/theorems/2ce827c7-4ace-44f3-86b1-6a959edb0d10
-- title:
--   BDL26 Two Sector Bad Projector: joint empty
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the joint empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L181-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L181-L184

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.joint_empty : Pjoint S n ∅ ∅ = 1 := by sorry
