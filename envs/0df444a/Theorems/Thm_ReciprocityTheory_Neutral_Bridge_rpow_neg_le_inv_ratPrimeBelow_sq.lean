-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_rpow_neg_le_inv_ratPrimeBelow_sq
-- name    : ReciprocityTheory.Neutral.Bridge.rpow_neg_le_inv_ratPrimeBelow_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:03.880681+00:00
-- url     : https://prove2.me/theorems/1e96b7ba-85d0-476a-b61e-d05cc59a232f
-- title:
--   Bridge: rpow neg le inv rat Prime Below sq
-- statement:
--   The Bridge construction uses the rpow neg le inv rat Prime Below sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L125-L137

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
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
variable {K : Type*} [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.rpow_neg_le_inv_ratPrimeBelow_sq (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / (ratPrimeBelow 𝔭 : ℝ) ^ 2 := by sorry
