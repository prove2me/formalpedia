-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_even_commute_selected_iff
-- name    : QEC.Coding.BDL26SectorTranslation.even_commute_selected_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:52:11.388222+00:00
-- url     : https://prove2.me/theorems/77c3eeb5-bb4a-4c80-bc90-ab3e763eae90
-- title:
--   BDL26 Sector Translation: even commute selected iff
-- statement:
--   The BDL26 Sector Translation construction uses the even commute selected iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L234-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L234-L237

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

theorem QEC.Coding.BDL26SectorTranslation.even_commute_selected_iff (k : Nat) (q : Physical S (2*k)) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S (2*k))) :
    Commute (coupling S (2*k) q a) (selected S (2*k) A) ↔
      translated S (2*k) q a A = A := by sorry
