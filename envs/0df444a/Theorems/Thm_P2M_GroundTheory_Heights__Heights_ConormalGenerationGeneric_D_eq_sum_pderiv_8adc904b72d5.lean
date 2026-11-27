-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_D_eq_sum_pderiv_8adc904b72d5
-- name    : P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_D_eq_sum_pderiv_8adc904b72d5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:00.928444+00:00
-- url     : https://prove2.me/theorems/0f3d8c13-3541-52c7-b5a7-6559a9e37243
-- title:
--   P2 M Ground Theory Heights  Heights Conormal Generation Generic D eq sum pderiv 8adc904b72d5: P2 M Ground Theory Heights  Heights Conormal Generation Generic D eq sum pderiv 8adc904b72d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Conormal Generation Generic D eq sum pderiv 8adc904b72d5 construction uses the P2 M Ground Theory Heights  Heights Conormal Generation Generic D eq sum pderiv 8adc904b72d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PConormalGenerationGeneric.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PConormalGenerationGeneric.lean#L12-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_D_eq_sum_pderiv_8adc904b72d5 {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    D ℂ (MvPolynomial (Fin n) ℂ) g = ∑ l, pderiv l g • D ℂ (MvPolynomial (Fin n) ℂ) (X l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConormalGenerationGeneric».«D_eq_sum_pderiv» := P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_D_eq_sum_pderiv_8adc904b72d5
