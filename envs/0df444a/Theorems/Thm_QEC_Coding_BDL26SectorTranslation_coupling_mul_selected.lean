-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_coupling_mul_selected
-- name    : QEC.Coding.BDL26SectorTranslation.coupling_mul_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:39:39.183966+00:00
-- url     : https://prove2.me/theorems/cf058296-7bf4-4ede-aa3c-dca0414f27a5
-- title:
--   BDL26 Sector Translation: coupling mul selected
-- statement:
--   The BDL26 Sector Translation construction uses the coupling mul selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L105-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L105-L109

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

theorem QEC.Coding.BDL26SectorTranslation.coupling_mul_selected (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (A : Finset (JointImage S n)) :
    coupling S n q a * selected S n A =
      selected S n (translated S n q a A) * coupling S n q a := by sorry
