-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_commute_goodJoint_iff
-- name    : QEC.Coding.BDL26SectorTranslation.commute_goodJoint_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T17:46:30.214696+00:00
-- url     : https://prove2.me/theorems/1de04b71-dbe8-40a4-9142-6549ba490e3a
-- title:
--   BDL26 Sector Translation: commute good Joint iff
-- statement:
--   Existing two-sector good selection, without a claim of decoder invariance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L204-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L204-L209

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

theorem QEC.Coding.BDL26SectorTranslation.commute_goodJoint_iff (q : Physical S n) (a : CSSDaviesLocality.Axis)
    (BX : Finset (XImage S n)) (BZ : Finset (ZImage S n)) :
    Commute (coupling S n q a) (Pjoint S n BX BZ) ↔
      BXᶜ = ∅ ∨ BZᶜ = ∅ ∨
        (translatedX S n q a BXᶜ = BXᶜ ∧ translatedZ S n q a BZᶜ = BZᶜ) := by sorry
