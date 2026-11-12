-- Prove2me | Theorems.Thm_QEC_Coding_BDL26SectorTranslation_coupling_mul_atom
-- name    : QEC.Coding.BDL26SectorTranslation.coupling_mul_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T17:46:07.418311+00:00
-- url     : https://prove2.me/theorems/372e8415-8908-477c-a083-519328b8fa75
-- title:
--   BDL26 Sector Translation: coupling mul atom
-- statement:
--   The BDL26 Sector Translation construction uses the coupling mul atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L99-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/SectorTranslation.lean#L99-L103

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

theorem QEC.Coding.BDL26SectorTranslation.coupling_mul_atom (q : Physical S n) (a : CSSDaviesLocality.Axis) (s : JointImage S n) :
    coupling S n q a * projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n) s) =
      projector S n (CSSGibbs.realizableEmbedding (zSyndrome S n) (xSyndrome S n)
        (translation S n q a s)) * coupling S n q a := by sorry
