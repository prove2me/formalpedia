-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_puncturedTriplePairing_eq_logical_delta_of_char_two
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.puncturedTriplePairing_eq_logical_delta_of_char_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:18:38.568664+00:00
-- url     : https://prove2.me/theorems/d16bf1bc-1fa5-46bb-9029-2e0e3d929a6a
-- title:
--   Ngu24 Multiplicative CCZ: punctured Triple Pairing eq logical delta of char two
-- statement:
--   The punctured basis representatives have the source's characteristic-two
--   cubic delta, derived rather than supplied as input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CCZIntertwining.lean#L151-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CCZIntertwining.lean#L151-L159

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics
open scoped BigOperators
open Ngu24MultiplicativeCSS
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_25
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_df646da45e_26
omit [Algebra (ZMod 2) F]

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.puncturedTriplePairing_eq_logical_delta_of_char_two
    (data : SourceInput F I Logical) [CharP F 2] (a b c : Logical)
    (h₁ h₂ h₃ : data.H0) :
    wordTriplePairing (data.shortenedCosetLabel (canonicalBasisWord (F := F) a) h₁)
      (data.shortenedCosetLabel (canonicalBasisWord (F := F) b) h₂)
      (data.shortenedCosetLabel (canonicalBasisWord (F := F) c) h₃) =
        if a = b ∧ b = c then 1 else 0 := by sorry
