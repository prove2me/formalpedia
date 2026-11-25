-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029
-- name    : P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:27.995695+00:00
-- url     : https://prove2.me/theorems/a678aaa9-818d-44db-8a42-cceab38a24d9
-- title:
--   P2 M Global Theory Det Ideal pow mem pow  741349ce2029: P2 M Global Theory Det Ideal pow mem pow  741349ce2029
-- statement:
--   The P2 M Global Theory Det Ideal pow mem pow  741349ce2029 construction uses the P2 M Global Theory Det Ideal pow mem pow  741349ce2029 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean#L49-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}

theorem P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029 (c : FractionalIdeal R⁰ K) {t : K} (ht : t ∈ c) (n : ℕ) : t ^ n ∈ c ^ n := by sorry

alias «GlobalTheory».«DetIdeal».«pow_mem_pow'» := P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029
