-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_adjoint
-- name    : QEC.Coding.BDL26CSSDaviesLocality.coupling_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:30:21.072915+00:00
-- url     : https://prove2.me/theorems/357d1d08-8c69-444b-9c41-15f66ce2c859
-- title:
--   BDL26 CSSDavies Locality: coupling adjoint
-- statement:
--   The BDL26 CSSDavies Locality construction uses the coupling adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L94-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/DaviesLocality.lean#L94-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_coupling_adjoint

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26CSSDaviesLocality.coupling_adjoint (q : Physical S n) (a : CSSDaviesLocality.Axis) :
    LinearMap.adjoint (coupling S n q a) = coupling S n q a := by sorry
