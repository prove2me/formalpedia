-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_deriv_prod_range_sub_mul_prod_ne_zero
-- name    : PositivityTheory.Rg.Sw.HSt.deriv_prod_range_sub_mul_prod_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:24.382358+00:00
-- url     : https://prove2.me/theorems/e9285fde-40a1-5444-af74-c1040e1246b8
-- title:
--   HSt: deriv prod range sub mul prod ne zero
-- statement:
--   The HSt construction uses the deriv prod range sub mul prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/DerivProdRangeSubMulProdNeZero.lean#L27-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/DerivProdRangeSubMulProdNeZero.lean#L27-L55

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_DerivProdRangeSubMulProdNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.HSt.deriv_prod_range_sub_mul_prod_ne_zero (n m : ℕ) (hmn : m < n) :
    deriv (fun z : ℂ => (∏ i ∈ Finset.range (n - m), ((i : ℂ) - z)) *
      (∏ i ∈ Finset.range (n - (n - m)), ((i : ℂ) - m - z))) 0 ≠ 0 := by sorry
