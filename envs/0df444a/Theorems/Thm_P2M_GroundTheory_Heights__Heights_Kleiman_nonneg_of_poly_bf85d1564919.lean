-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:33.170384+00:00
-- url     : https://prove2.me/theorems/fc330326-a1e9-44a4-ae2c-f0635793755f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman nonneg of poly bf85d1564919: P2 M Ground Theory Heights  Heights Kleiman nonneg of poly bf85d1564919
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman nonneg of poly bf85d1564919 construction uses the P2 M Ground Theory Heights  Heights Kleiman nonneg of poly bf85d1564919 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L67-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L67-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919 {e : ℕ} (c : Finset (Fin e) → ℤ)
    (h : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin e), (q : ℤ) ^ Sᶜ.card * c S) : 0 ≤ c ∅ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«nonneg_of_poly» := P2M_GroundTheory_Heights__Heights_Kleiman_nonneg_of_poly_bf85d1564919
