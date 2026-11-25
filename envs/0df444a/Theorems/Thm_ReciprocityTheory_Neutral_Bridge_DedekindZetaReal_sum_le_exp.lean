-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_le_exp
-- name    : ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_exp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:37.70647+00:00
-- url     : https://prove2.me/theorems/f57f73a4-e7a2-42d1-b960-761b52823cf7
-- title:
--   Dedekind Zeta Real: sum le exp
-- statement:
--   The Dedekind Zeta Real construction uses the sum le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L199-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L199-L219

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

theorem ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_exp {s : ℝ} (hs : 1 < s) (T : Finset (Ideal (𝓞 K))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
      Real.exp (2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by sorry
