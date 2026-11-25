-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_natCard_homology_of_shortExact_mul__238aab7615a5
-- name    : P2M_GlobalTheory_T_natCard_homology_of_shortExact_mul__238aab7615a5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:09.843682+00:00
-- url     : https://prove2.me/theorems/51b055cf-d299-4848-b8c9-35de0bf0c47c
-- title:
--   P2 M Global Theory T nat Card homology of short Exact mul  238aab7615a5: P2 M Global Theory T nat Card homology of short Exact mul  238aab7615a5
-- statement:
--   The P2 M Global Theory T nat Card homology of short Exact mul  238aab7615a5 construction uses the P2 M Global Theory T nat Card homology of short Exact mul  238aab7615a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_natCard_homology_of_shortExact_mul__238aab7615a5 : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by sorry

alias «GlobalTheory».«T».«natCard_homology_of_shortExact_mul'» := P2M_GlobalTheory_T_natCard_homology_of_shortExact_mul__238aab7615a5
