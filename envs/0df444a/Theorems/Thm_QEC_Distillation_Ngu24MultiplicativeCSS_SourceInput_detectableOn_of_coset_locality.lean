-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_detectableOn_of_coset_locality
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.detectableOn_of_coset_locality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:11:33.540066+00:00
-- url     : https://prove2.me/theorems/15a78ee7-539e-45a9-871f-aabecba0ca42
-- title:
--   Source Input: detectable On of coset locality
-- statement:
--   Complement separation and local interpolation prove detectability on the
--   entire semantic range carrier, not only on its computational codewords.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L120-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CosetDetectability.lean#L120-L164

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.detectableOn_of_coset_locality (data : SourceInput F I Logical)
    (E : Operator (ComputationalBasisRegister F data.PivotComplement))
    (S : Finset data.PivotComplement)
    (hsep : ∀ u v h k,
      (∀ j, j ∉ S → data.shortenedCosetLabel u h j = data.shortenedCosetLabel v k j) →
        u = v ∧ h = k)
    (honto : Function.Surjective (fun h : data.H0 =>
      fun j : S => data.puncture h.val.val j.val))
    (hlocal : ∀ x y : Word F data.PivotComplement,
      (∃ j, j ∉ S ∧ x j ≠ y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet y)) = 0)
    (hdiag : ∀ x y : Word F data.PivotComplement,
      (∀ j, j ∈ S → x j = y j) →
        inner Complex (registerBasisKet x) (E (registerBasisKet x)) =
          inner Complex (registerBasisKet y) (E (registerBasisKet y))) :
    DetectableOn data.quantumCode E := by sorry
