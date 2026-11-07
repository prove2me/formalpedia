-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_adjoint
-- name    : QEC.Coding.CSSDaviesLocality.coupling_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:41:34.872529+00:00
-- url     : https://prove2.me/theorems/7453ffec-cf46-4229-9540-c65a66af76ee
-- title:
--   CSSDavies Locality: coupling adjoint
-- statement:
--   The CSSDavies Locality construction uses the coupling adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L84-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L84-L85

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.CSSDaviesLocality.coupling_adjoint (q : ι) (a : Axis) : LinearMap.adjoint (coupling q a) = coupling q a := by sorry
