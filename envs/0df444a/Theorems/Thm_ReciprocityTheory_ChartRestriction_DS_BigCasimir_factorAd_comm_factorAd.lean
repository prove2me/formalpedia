-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_comm_factorAd
-- name    : ReciprocityTheory.ChartRestriction.DS.BigCasimir.factorAd_comm_factorAd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:51.036919+00:00
-- url     : https://prove2.me/theorems/9ef6b336-10fc-4952-946d-dcf2b5205a07
-- title:
--   Big Casimir: factor Ad comm factor Ad
-- statement:
--   The Big Casimir construction uses the factor Ad comm factor Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/BigCasA.lean#L98-L104

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

theorem ReciprocityTheory.ChartRestriction.DS.BigCasimir.factorAd_comm_factorAd {k : ℕ} {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by sorry
