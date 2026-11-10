-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_hamiltonian_commute
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:29:12.388865+00:00
-- url     : https://prove2.me/theorems/6f3b611b-ea5a-482e-82ab-ee4e531a667a
-- title:
--   BDL26 Two Sector Bad Projector: hamiltonian commute
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the hamiltonian commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L102-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L102-L104

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute (A : Finset (JointImage S n)) :
    Commute (hamiltonian S n) (selected S n A) := by sorry
