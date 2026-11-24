-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:14.522367+00:00
-- url     : https://prove2.me/theorems/3580b8e9-60af-440b-ae4c-d9772ec74961
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds sum rpow neg le pow add2b3ef4a0c: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds sum rpow neg le pow add2b3ef4a0c
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds sum rpow neg le pow add2b3ef4a0c construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds sum rpow neg le pow add2b3ef4a0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L167-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L167-L207

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c (T : Finset (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ∑ I ∈ T, (absNorm I : ℝ) ^ (-s) ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«sum_rpow_neg_le_pow» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_sum_rpow_neg_le_pow_add2b3ef4a0c
