-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_dvd_of_period_of_dvd_sum_powersetCard__220d956ab7d3
-- name    : P2M_GlobalTheory_T_dvd_of_period_of_dvd_sum_powersetCard__220d956ab7d3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:48.885202+00:00
-- url     : https://prove2.me/theorems/ab4419ff-8e4b-4ae1-bb90-272cb85a5522
-- title:
--   P2 M Global Theory T dvd of period of dvd sum powerset Card  220d956ab7d3: P2 M Global Theory T dvd of period of dvd sum powerset Card  220d956ab7d3
-- statement:
--   The P2 M Global Theory T dvd of period of dvd sum powerset Card  220d956ab7d3 construction uses the P2 M Global Theory T dvd of period of dvd sum powerset Card  220d956ab7d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCardStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCardStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_dvd_of_period_of_dvd_sum_powersetCard__220d956ab7d3 : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → (∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i)) → ∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l := by sorry

alias «GlobalTheory».«T».«dvd_of_period_of_dvd_sum_powersetCard'» := P2M_GlobalTheory_T_dvd_of_period_of_dvd_sum_powersetCard__220d956ab7d3
