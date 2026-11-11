-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_commute_PZ_iff
-- name    : QEC.Coding.BDL26SectorTranslation.commute_PZ_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:48:50.930657+00:00
-- url     : https://prove2.me/theorems/eab215af-d79e-43dc-93d1-4a992a8d89ac
-- title:
--   BDL26 Sector Translation: commute PZ iff
-- statement:
--   The BDL26 Sector Translation construction uses the commute PZ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L217-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L217-L221

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

theorem QEC.Coding.BDL26SectorTranslation.commute_PZ_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (BZ : Finset (ZImage S n)) :
    Commute (coupling S n q a) (PZ S n BZ) ↔
      translated S n q a (goodZ S n BZ) = goodZ S n BZ := by sorry
