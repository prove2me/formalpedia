-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_logicalBasisTriplePairing_eq_delta
-- name    : QEC.Distillation.Ngu24MultiplicativeCCZ.logicalBasisTriplePairing_eq_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:18:16.517824+00:00
-- url     : https://prove2.me/theorems/c18e82d9-549a-4b10-a3ca-f23d17fa208b
-- title:
--   Ngu24 Multiplicative CCZ: logical Basis Triple Pairing eq delta
-- statement:
--   The logical basis cubic pairing is the diagonal Kronecker delta.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CCZIntertwining.lean#L129-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CCZIntertwining.lean#L129-L146

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
omit [Fintype F] [Algebra (ZMod 2) F]

theorem QEC.Distillation.Ngu24MultiplicativeCCZ.logicalBasisTriplePairing_eq_delta (a b c : Logical) :
    wordTriplePairing (canonicalBasisWord (F := F) a) (canonicalBasisWord (F := F) b)
      (canonicalBasisWord (F := F) c) = if a = b ∧ b = c then 1 else 0 := by sorry
