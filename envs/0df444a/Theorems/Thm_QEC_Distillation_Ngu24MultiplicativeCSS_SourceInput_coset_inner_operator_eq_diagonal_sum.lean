-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_inner_operator_eq_diagonal_sum
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_inner_operator_eq_diagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:10:38.342318+00:00
-- url     : https://prove2.me/theorems/e803f609-95c4-47c7-9492-2702fcaea4cf
-- title:
--   Source Input: coset inner operator eq diagonal sum
-- statement:
--   Complement separation reduces each diagonal logical matrix element to
--   the actual single sum of local computational-basis expectations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L57-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L57-L82

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_inner_operator_eq_diagonal_sum (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (u : Word F Logical) :
    inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet u)) =
      star (cosetNormalization data.H0) * cosetNormalization data.H0 *
        ∑ h : data.H0, inner Complex (registerBasisKet (data.shortenedCosetLabel u h))
          (E (registerBasisKet (data.shortenedCosetLabel u h))) := by sorry
