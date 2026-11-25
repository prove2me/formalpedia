-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_isGlRep_factorAd
-- name    : ReciprocityTheory.ChartRestriction.DS.BigCasimir.isGlRep_factorAd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:41.912801+00:00
-- url     : https://prove2.me/theorems/bbfabce2-cfe2-4b72-8118-aad90d9df46c
-- title:
--   Big Casimir: is Gl Rep factor Ad
-- statement:
--   The Big Casimir construction uses the is Gl Rep factor Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L114-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.BigCasimir.isGlRep_factorAd (k : ℕ) (i : Fin k) : IsGlRep (n := n) (fun a b => factorAd (M := M) k i a b) := by sorry
