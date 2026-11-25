-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_summable_absNorm_rpow
-- name    : ReciprocityTheory.Neutral.Bridge.summable_absNorm_rpow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:50.132645+00:00
-- url     : https://prove2.me/theorems/0dd55fa9-102a-4e0b-8a08-cf7d86104b07
-- title:
--   Bridge: summable abs Norm rpow
-- statement:
--   The Bridge construction uses the summable abs Norm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TendstoPrimeIdealZetaSumUniv.lean#L170-L176

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

theorem ReciprocityTheory.Neutral.Bridge.summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by sorry
