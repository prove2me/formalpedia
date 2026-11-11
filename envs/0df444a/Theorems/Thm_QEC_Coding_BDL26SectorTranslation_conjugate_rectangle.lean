-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_conjugate_rectangle
-- name    : QEC.Coding.BDL26SectorTranslation.conjugate_rectangle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:47:48.537832+00:00
-- url     : https://prove2.me/theorems/281edc19-48c0-422f-9582-5d99f2e3c673
-- title:
--   BDL26 Sector Translation: conjugate rectangle
-- statement:
--   The BDL26 Sector Translation construction uses the conjugate rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L143-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L143-L147

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

theorem QEC.Coding.BDL26SectorTranslation.conjugate_rectangle (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (XImage S n)) (B : Finset (ZImage S n)) :
    coupling S n q a * selected S n (A ×ˢ B) * coupling S n q a =
      selected S n (translatedX S n q a A ×ˢ translatedZ S n q a B) := by sorry
