-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_diagonal_sum_eq_zero_label
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_diagonal_sum_eq_zero_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:10:56.139511+00:00
-- url     : https://prove2.me/theorems/c0e9a674-5451-4a19-b789-f9314b3525ec
-- title:
--   Source Input: coset diagonal sum eq zero label
-- statement:
--   Translation of the actual kernel sum removes the logical representative
--   from every locally supported diagonal expectation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L86-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L86-L116

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput._p2m_local_instance_b70f205f2b_25

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_diagonal_sum_eq_zero_label (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y)))
    (u : Word F Logical) :
    (∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
      (E (registerBasisKet (data.shortenedCosetLabel u h)))) =
    ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel 0 h))
      (E (registerBasisKet (data.shortenedCosetLabel 0 h))) := by sorry
