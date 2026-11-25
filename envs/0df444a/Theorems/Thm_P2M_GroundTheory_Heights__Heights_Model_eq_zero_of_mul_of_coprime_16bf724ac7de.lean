-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de
-- name    : P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:51.802081+00:00
-- url     : https://prove2.me/theorems/b750a4ad-65aa-48e1-af24-1c2cfb2ecd1c
-- title:
--   P2 M Ground Theory Heights  Heights Model eq zero of mul of coprime 16bf724ac7de: P2 M Ground Theory Heights  Heights Model eq zero of mul of coprime 16bf724ac7de
-- statement:
--   The P2 M Ground Theory Heights  Heights Model eq zero of mul of coprime 16bf724ac7de construction uses the P2 M Ground Theory Heights  Heights Model eq zero of mul of coprime 16bf724ac7de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L12-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de {B : Type*} [CommRing B] (p : ℕ) (hp : p.Prime) (e N' : ℕ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hN' : IsUnit (N' : B)) (t : B)
    (h1 : ((p ^ e * N' : ℕ) : B) * t = 0) (h2 : (u : B) * t = 0) : t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«eq_zero_of_mul_of_coprime» := P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_mul_of_coprime_16bf724ac7de
