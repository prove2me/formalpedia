-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_mixedDiff_precomp_c1f3f1b7faf4
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_mixedDiff_precomp_c1f3f1b7faf4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:37.765576+00:00
-- url     : https://prove2.me/theorems/6e75ac0d-a7df-4a6d-92d7-f4e53f4fefd3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Relabel mixed Diff precomp c1f3f1b7faf4: P2 M Ground Theory Heights  Heights Field Numbers Relabel mixed Diff precomp c1f3f1b7faf4
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Relabel mixed Diff precomp c1f3f1b7faf4 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Relabel mixed Diff precomp c1f3f1b7faf4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/IntNumRelabel.lean#L52-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
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
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_mixedDiff_precomp_c1f3f1b7faf4 {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«Relabel».«mixedDiff_precomp» := P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_mixedDiff_precomp_c1f3f1b7faf4
