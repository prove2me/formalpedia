-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteAlphabet_localOperator_basis_inner
-- name    : QEC.Semantics.FiniteAlphabet.localOperator_basis_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:08:40.1874+00:00
-- url     : https://prove2.me/theorems/acc5d745-390f-475e-b887-89fae9334d5b
-- title:
--   Finite Alphabet: local Operator basis inner
-- statement:
--   The selected/complement tensor factors give the actual local matrix element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L55-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteAlphabetLocality.lean#L55-L80

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

theorem QEC.Semantics.FiniteAlphabet.localOperator_basis_inner (S : QuditSubsystem (fun _ : I => Fintype.card A))
    (E : Operator S.selectedSystem) (x y : I → A) :
    inner Complex (EuclideanSpace.basisFun (I → A) Complex x)
      (localOperator S E (EuclideanSpace.basisFun (I → A) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I x)).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel (labelEquiv A I y)).2) := by sorry
