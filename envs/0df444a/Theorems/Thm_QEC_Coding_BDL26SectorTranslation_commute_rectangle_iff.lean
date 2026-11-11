-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_commute_rectangle_iff
-- name    : QEC.Coding.BDL26SectorTranslation.commute_rectangle_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:41:23.528206+00:00
-- url     : https://prove2.me/theorems/0940a9b7-cb4a-4584-98a2-24afd607c1dd
-- title:
--   BDL26 Sector Translation: commute rectangle iff
-- statement:
--   Empty factors give the zero operator; otherwise both factors must be invariant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L183-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L183-L201

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26SectorTranslation
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26CSSDaviesLocality BDL26TwoSectorBadProjector
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26SectorTranslation._p2m_local_instance_8726da3c88_19
attribute [local instance] QEC.Coding.BDL26SectorTranslation._p2m_local_instance_8726da3c88_20

theorem QEC.Coding.BDL26SectorTranslation.commute_rectangle_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    Commute (coupling S n q a) (selected S n (A ×ˢ B)) ↔
      A = ∅ ∨ B = ∅ ∨ (translatedX S n q a A = A ∧ translatedZ S n q a B = B) := by sorry
