-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:54.515827+00:00
-- url     : https://prove2.me/theorems/5437f1f5-b52d-4760-ae57-dd42dfe9144d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel injective 9aa4aa668bcb: P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel injective 9aa4aa668bcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel injective 9aa4aa668bcb construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lex Relabel injective 9aa4aa668bcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L42-L46

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«lexRelabel_injective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_lexRelabel_injective_9aa4aa668bcb
