-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:04.3438+00:00
-- url     : https://prove2.me/theorems/2fe45ef5-0149-4bf3-bb8b-d621f16c7570
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel surjective 57cbea4d2428: P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel surjective 57cbea4d2428
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel surjective 57cbea4d2428 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel surjective 57cbea4d2428 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L36-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
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
open MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428 (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«lexRelabel_surjective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_surjective_57cbea4d2428
