-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TwoSectorBadProjector_tail_two_bounds
-- name    : QEC.Coding.BDL26TwoSectorBadProjector.tail_two_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:23:33.889884+00:00
-- url     : https://prove2.me/theorems/c22bcad3-e889-440e-8232-6ac59c67388a
-- title:
--   BDL26 Two Sector Bad Projector: tail two bounds
-- statement:
--   The BDL26 Two Sector Bad Projector construction uses the tail two bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L176-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/TwoSectorBadProjector.lean#L176-L179

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

theorem QEC.Coding.BDL26TwoSectorBadProjector.tail_two_bounds (β εX εZ : ℝ) (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n))
    (hX : pX S n β BX ≤ εX) (hZ : pZ S n β BZ ≤ εZ) :
    clbtGibbsTailMass (Pjoint S n BX BZ) (gibbs S n β) ≤ εX+εZ := by sorry
