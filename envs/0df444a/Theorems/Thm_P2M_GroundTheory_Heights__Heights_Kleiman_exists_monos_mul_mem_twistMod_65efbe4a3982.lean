-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:35:36.045438+00:00
-- url     : https://prove2.me/theorems/56268c76-7172-4069-8026-38700cc7429d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod 65efbe4a3982: P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod 65efbe4a3982
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod 65efbe4a3982 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists monos mul mem twist Mod 65efbe4a3982 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L32-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982 (I K : Chart x) (b : Ω)
    (hb : b ∈ chartRing S x (chartUnion I K)) :
    ∃ u ∈ monos (S := S) I.1, ∃ d : ℕ, u.IsHomogeneous d ∧ aeval x u * b ∈ twistMod S x (d : ℤ) K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_monos_mul_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982
