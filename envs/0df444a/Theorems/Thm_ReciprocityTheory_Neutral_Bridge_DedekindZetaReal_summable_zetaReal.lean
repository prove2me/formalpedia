-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_summable_zetaReal
-- name    : ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.summable_zetaReal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:10.321797+00:00
-- url     : https://prove2.me/theorems/12c63870-96a9-593d-931e-4873da909549
-- title:
--   Dedekind Zeta Real: summable zeta Real
-- statement:
--   The Dedekind Zeta Real construction uses the summable zeta Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L40-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal

theorem ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.summable_zetaReal {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by sorry
