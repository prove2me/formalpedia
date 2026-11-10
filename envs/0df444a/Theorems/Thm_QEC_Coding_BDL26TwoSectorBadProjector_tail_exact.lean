-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_exact
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.tail_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:01:35.129502+00:00
-- url     : https://prove2.me/theorems/eb77b03a-3779-4fd1-9475-a35fd3ff5c7b
-- title:
--   BDL26 Two Sector Bad Projector: tail exact
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the tail exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L158-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L158-L162

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.tail_exact (β : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) =
      pX S n β BX+pZ S n β BZ-pX S n β BX*pZ S n β BZ := by sorry
