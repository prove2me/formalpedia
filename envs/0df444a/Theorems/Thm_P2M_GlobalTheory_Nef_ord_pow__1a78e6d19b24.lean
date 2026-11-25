-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Nef_ord_pow__1a78e6d19b24
-- name    : P2M_GlobalTheory_Nef_ord_pow__1a78e6d19b24
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:21.243+00:00
-- url     : https://prove2.me/theorems/a9d06559-656b-4405-84a9-05f6aff3770c
-- title:
--   P2 M Global Theory Nef ord pow  1a78e6d19b24: P2 M Global Theory Nef ord pow  1a78e6d19b24
-- statement:
--   The P2 M Global Theory Nef ord pow  1a78e6d19b24 construction uses the P2 M Global Theory Nef ord pow  1a78e6d19b24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeSymmetricPowerFamily.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdmissibleDegreeSymmetricPowerFamily.lean#L46-L48

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdmissibleDegreeSymmetricPowerFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef

theorem P2M_GlobalTheory_Nef_ord_pow__1a78e6d19b24 {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (N : ℕ) :
    ord v (x ^ N) = (N : ℤ) * ord v x := by sorry

alias «GlobalTheory».«Nef».«ord_pow'» := P2M_GlobalTheory_Nef_ord_pow__1a78e6d19b24
