-- Prove2me | Theorems.Thm_QEC_Coding_Why24AppendixANF_wordMul_eq_sum
-- name    : QEC.Coding.Why24AppendixANF.wordMul_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:07:29.395824+00:00
-- url     : https://prove2.me/theorems/4ce20696-7e4d-4724-936e-66cc5e3fdbc8
-- title:
--   Why24 Appendix ANF: word Mul eq sum
-- statement:
--   The Why24 Appendix ANF construction uses the word Mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L235-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Field.lean#L235-L242

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix

theorem QEC.Coding.Why24AppendixANF.wordMul_eq_sum (left right : Word) :
    wordMul left right =
      ∑ first : Fin 10, ∑ second : Fin 10,
        (left first * right second) •
          alphaReduction
            ⟨(first : Nat) + (second : Nat), by omega⟩ := by sorry
