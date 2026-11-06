-- Prove2me | Theorems.Thm_QEC_Coding_hammingSupport_smul_subset
-- name    : QEC.Coding.hammingSupport_smul_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:56.359664+00:00
-- url     : https://prove2.me/theorems/14c32528-9f69-4773-b601-ad3be06b7e17
-- title:
--   Coding: hamming Support smul subset
-- statement:
--   The Coding construction uses the hamming Support smul subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L18-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Distance.lean#L18-L27

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w

theorem QEC.Coding.hammingSupport_smul_subset
    {F : Type u} [Field F]
    {ι : Type v} [Fintype ι] [DecidableEq F]
    (a : F) (x : Word F ι) :
    hammingSupport (a • x) ⊆ hammingSupport x := by sorry
