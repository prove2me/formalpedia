-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_isIntegral_int_of_rmu
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.isIntegral_int_of_rmu
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:51.72241+00:00
-- url     : https://prove2.me/theorems/0203a178-d0e5-429e-916a-ca9754409ffa
-- title:
--   KE: is Integral int of rmu
-- statement:
--   The KE construction uses the is Integral int of rmu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L137-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L137-L143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.KE.isIntegral_int_of_rmu (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by sorry
