-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:01.276396+00:00
-- url     : https://prove2.me/theorems/e6492534-68e6-414e-9163-7eab7c78c589
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES alt sum e5d5b5b56ff0: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES alt sum e5d5b5b5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES alt sum e5d5b5b56ff0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES alt sum e5d5b5b56ff0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L344-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L344-L357

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0 (a b c i p r : ℕ → ℤ) (h0 : a 0 = i 0) (hs : ∀ n, a (n + 1) = i (n + 1) + r n)
    (hb : ∀ n, b n = p n + i n) (hc : ∀ n, c n = r n + p n) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n + ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n +
        (-1) ^ (N + 1) * r N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«alt_sum» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0
