-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_coset_inner_operator_eq_zero
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_inner_operator_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:10:29.504993+00:00
-- url     : https://prove2.me/theorems/0fc8fafb-06e8-43b3-a96b-fbdeaa85cd5f
-- title:
--   Source Input: coset inner operator eq zero
-- statement:
--   Once complementary coordinates distinguish all coset summands, a local
--   operator has no off-diagonal logical matrix elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L29-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L29-L53

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.coset_inner_operator_eq_zero (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (u v : Word F Logical) (huv : u ≠ v) :
    inner Complex (data.shortenedCosetKet u) (E (data.shortenedCosetKet v)) = 0 := by sorry
