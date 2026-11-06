-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteAlphabet_detectableOn_transport_of_localOperator
-- name    : QEC.Semantics.FiniteAlphabet.detectableOn_transport_of_localOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:16:13.006107+00:00
-- url     : https://prove2.me/theorems/2067367e-00e5-4bfd-a1c4-1abdd96660bb
-- title:
--   Finite Alphabet: detectable On transport of local Operator
-- statement:
--   Native-alphabet detection is detection of the actual tensor-local operator
--   on the canonically relabelled quantum code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L116-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L116-L131

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.FiniteAlphabet
open scoped BigOperators TensorProduct
universe u
variable (A I : Type u) [Fintype A] [Fintype I] [DecidableEq I]
attribute [local instance] QEC.Semantics.FiniteAlphabet._p2m_local_instance_ac378d2a8a_23
variable {A I}

theorem QEC.Semantics.FiniteAlphabet.detectableOn_transport_of_localOperator
    (C : QuantumCode (EuclideanSpace Complex (I → A)))
    (S : QuditSubsystem (fun _ : I => Fintype.card A)) (E : Operator S.selectedSystem)
    (h : DetectableOn C (localOperator S E)) :
    DetectableOn (C.transport (registerUnitary A I)) (S.extendLocalToRegister E) := by sorry
