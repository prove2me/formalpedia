-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:18.413404+00:00
-- url     : https://prove2.me/theorems/0f27fda0-9389-4187-b2e9-bf9c551675e3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res x Prod ne zero 02420b01a7e4: P2 M Ground Theory Heights  Heights Kleiman res x Prod ne zero 02420b01a7e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res x Prod ne zero 02420b01a7e4 construction uses the P2 M Ground Theory Heights  Heights Kleiman res x Prod ne zero 02420b01a7e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L125-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L125-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4 (I : Chart x) : xProd I ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_xProd_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4
