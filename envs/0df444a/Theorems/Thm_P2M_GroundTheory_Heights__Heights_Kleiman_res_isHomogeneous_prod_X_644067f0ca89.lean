-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_isHomogeneous_prod_X_644067f0ca89
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_isHomogeneous_prod_X_644067f0ca89
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:24.153801+00:00
-- url     : https://prove2.me/theorems/7bea26fb-a845-479a-9de4-c40b8dd8fdb8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res is Homogeneous prod X 644067f0ca89: P2 M Ground Theory Heights  Heights Kleiman res is Homogeneous prod X 644067f0ca89
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res is Homogeneous prod X 644067f0ca89 construction uses the P2 M Ground Theory Heights  Heights Kleiman res is Homogeneous prod X 644067f0ca89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L115-L119

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_isHomogeneous_prod_X_644067f0ca89 (s : Finset (Fin (N + 1))) :
    (∏ i ∈ s, (X i : Poly S N)).IsHomogeneous s.card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_isHomogeneous_prod_X» := P2M_GroundTheory_Heights__Heights_Kleiman_res_isHomogeneous_prod_X_644067f0ca89
