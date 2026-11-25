-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:07.921017+00:00
-- url     : https://prove2.me/theorems/ae5a6fe5-7454-5a98-a678-576213306465
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mixed Diff prod Fn 9c9c9edb0e49: P2 M Ground Theory Heights  Heights Field Numbers mixed Diff prod Fn 9c9c9edb0e49
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mixed Diff prod Fn 9c9c9edb0e49 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mixed Diff prod Fn 9c9c9edb0e49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L77-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L77-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49 {m r : ℕ} (cs : Fin r → K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    mixedDiff (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
        (fun i => pullDeg Function.Embedding.some (cs i))) (prodFn A B) =
      prodFn (mixedDiff cs A) (diff1^[m] B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mixedDiff_prodFn» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_prodFn_9c9c9edb0e49
