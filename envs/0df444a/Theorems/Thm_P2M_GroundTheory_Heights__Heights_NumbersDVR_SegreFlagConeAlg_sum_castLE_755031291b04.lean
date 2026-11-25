-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:46.655311+00:00
-- url     : https://prove2.me/theorems/548811da-4a7a-4ca3-b176-c5a6e22694e1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg sum cast LE 755031291b04: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg sum cast LE 755031291b04
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg sum cast LE 755031291b04 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg sum cast LE 755031291b04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L15-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04 {M : Type*} [AddCommMonoid M] {N k : ℕ} (hkN : k ≤ N) (s : Fin N → M)
    (hs : ∀ j : Fin N, k ≤ (j : ℕ) → s j = 0) : ∑ j, s j = ∑ j : Fin k, s (Fin.castLE hkN j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagConeAlg».«sum_castLE» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_sum_castLE_755031291b04
