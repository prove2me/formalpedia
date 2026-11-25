-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_relIndex_oneUnits_mul_eq_card_quotient__e71c35adc924
-- name    : P2M_GlobalTheory_T_relIndex_oneUnits_mul_eq_card_quotient__e71c35adc924
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:12.164915+00:00
-- url     : https://prove2.me/theorems/6af21b3f-eec4-4984-8857-aa810bdca960
-- title:
--   P2 M Global Theory T rel Index one Units mul eq card quotient  e71c35adc924: P2 M Global Theory T rel Index one Units mul eq card quotient  e71c35adc924
-- statement:
--   The P2 M Global Theory T rel Index one Units mul eq card quotient  e71c35adc924 construction uses the P2 M Global Theory T rel Index one Units mul eq card quotient  e71c35adc924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexOneUnitsMulEqCardQuotientStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexOneUnitsMulEqCardQuotientStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotientStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_relIndex_oneUnits_mul_eq_card_quotient__e71c35adc924 : ∀ (O : Type) [CommRing O] [IsDomain O] (t s : O), t ≠ 0 → s ∣ t → Ideal.span {t} ≤ Ideal.jacobson (⊥ : Ideal O) → (oneUnits (s * t)).relIndex (oneUnits t) = Nat.card (O ⧸ Ideal.span {s}) := by sorry

alias «GlobalTheory».«T».«relIndex_oneUnits_mul_eq_card_quotient'» := P2M_GlobalTheory_T_relIndex_oneUnits_mul_eq_card_quotient__e71c35adc924
