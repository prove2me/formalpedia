-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_card_eq
-- name    : ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_card_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:07.732799+00:00
-- url     : https://prove2.me/theorems/f2f741f2-3ea9-536c-a107-707db97002f9
-- title:
--   Dedekind Zeta Real: sum card eq
-- statement:
--   The Dedekind Zeta Real construction uses the sum card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L221-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L221-L237

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
open DedekindZetaReal
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal

theorem ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_card_eq {s : ℝ} (u : Finset ℕ) :
    ∑ n ∈ u, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) =
      ∑ I ∈ u.biUnion (fun n ↦ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset),
        (Ideal.absNorm I : ℝ) ^ (-s) := by sorry
