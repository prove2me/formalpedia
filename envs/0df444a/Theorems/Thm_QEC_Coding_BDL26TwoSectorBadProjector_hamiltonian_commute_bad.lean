-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_hamiltonian_commute_bad
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute_bad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T14:22:17.908379+00:00
-- url     : https://prove2.me/theorems/e1584b2a-bde2-472c-a0c6-2dd97bd8a505
-- title:
--   BDL26 Two Sector Bad Projector: hamiltonian commute bad
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the hamiltonian commute bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L109-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L109-L111

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.hamiltonian_commute_bad (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (hamiltonian S n) (1 - Pjoint S n BX BZ) := by sorry
