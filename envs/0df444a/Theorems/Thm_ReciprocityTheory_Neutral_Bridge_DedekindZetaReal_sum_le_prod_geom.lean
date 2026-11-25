-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_sum_le_prod_geom
-- name    : ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_prod_geom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:48.599207+00:00
-- url     : https://prove2.me/theorems/ab63a5f7-fecb-439e-992f-bebbabdd779b
-- title:
--   Dedekind Zeta Real: sum le prod geom
-- statement:
--   The Dedekind Zeta Real construction uses the sum le prod geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L104-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L104-L164

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

theorem ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_prod_geom {s : ℝ} (hs : 0 < s) (T : Finset (Ideal (𝓞 K))) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)), ∃ B : ℕ,
      ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
        ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k := by sorry
