-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_translation_bijective
-- name    : QEC.Coding.BDL26SectorTranslation.translation_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:44:10.23776+00:00
-- url     : https://prove2.me/theorems/ec15abce-d84c-4e43-bce2-1a215ce36a27
-- title:
--   BDL26 Sector Translation: translation bijective
-- statement:
--   The BDL26 Sector Translation construction uses the translation bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L37-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L37-L38

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

theorem QEC.Coding.BDL26SectorTranslation.translation_bijective (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    Function.Bijective (translation S n q a) := by sorry
