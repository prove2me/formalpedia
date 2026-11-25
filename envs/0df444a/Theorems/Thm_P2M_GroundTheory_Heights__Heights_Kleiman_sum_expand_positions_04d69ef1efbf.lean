-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:12:40.234889+00:00
-- url     : https://prove2.me/theorems/468b29d7-6fd2-5d86-b9b1-2e4617ddba4a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sum expand positions 04d69ef1efbf: P2 M Ground Theory Heights  Heights Kleiman sum expand positions 04d69ef1efbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sum expand positions 04d69ef1efbf construction uses the P2 M Ground Theory Heights  Heights Kleiman sum expand positions 04d69ef1efbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L15-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L15-L65

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf {X : Type*} {e : ℕ} (Φ : (Fin e → X) → ℤ) (V M A : Fin e → X) (a b : Fin e → ℤ)
    (hposition : ∀ (L : Fin e → X) (i : Fin e), Φ (Function.update L i (V i)) =
      a i * Φ (Function.update L i (M i)) + b i * Φ (Function.update L i (A i))) :
    Φ V = ∑ S : Finset (Fin e), (∏ i ∈ S, b i) * (∏ i ∈ Sᶜ, a i) *
      Φ (fun i => if i ∈ S then A i else M i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sum_expand_positions» := P2M_GroundTheory_Heights__Heights_Kleiman_sum_expand_positions_04d69ef1efbf
