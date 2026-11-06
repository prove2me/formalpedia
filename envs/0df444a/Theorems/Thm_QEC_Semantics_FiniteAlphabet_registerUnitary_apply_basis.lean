-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteAlphabet_registerUnitary_apply_basis
-- name    : QEC.Semantics.FiniteAlphabet.registerUnitary_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:12.709823+00:00
-- url     : https://prove2.me/theorems/1906dc4a-a637-496f-bb22-7932fb6442e1
-- title:
--   Finite Alphabet: register Unitary apply basis
-- statement:
--   The Finite Alphabet construction uses the register Unitary apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L38-L45

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

theorem QEC.Semantics.FiniteAlphabet.registerUnitary_apply_basis (x : I → A) :
    registerUnitary A I (EuclideanSpace.basisFun (I → A) Complex x) =
      EuclideanSpace.basisFun (Qudit.Label (fun _ : I => Fintype.card A)) Complex
        (labelEquiv A I x) := by sorry
