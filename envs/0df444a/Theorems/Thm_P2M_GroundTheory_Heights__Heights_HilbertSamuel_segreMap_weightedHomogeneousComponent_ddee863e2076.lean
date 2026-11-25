-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_weightedHomogeneousComponent_ddee863e2076
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_weightedHomogeneousComponent_ddee863e2076
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:07.396423+00:00
-- url     : https://prove2.me/theorems/297abcca-e2e8-4167-87c6-c11a37e8181d
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map weighted Homogeneous Component ddee863e2076: P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map weighted Homogeneous Component dd
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map weighted Homogeneous Component ddee863e2076 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map weighted Homogeneous Component ddee863e2076 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSegrePrime.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSegrePrime.lean#L38-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegrePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_weightedHomogeneousComponent_ddee863e2076 [Nonempty K] (b : Unit → ℕ)
    (g : MRing (fun _ : Unit => ∀ k, ι k) F) :
    segreMap F (weightedHomogeneousComponent (blockWeight (fun _ : Unit => ∀ k, ι k)) b g) =
      weightedHomogeneousComponent (blockWeight ι) (fun _ => b ()) (segreMap F g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«segreMap_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_weightedHomogeneousComponent_ddee863e2076
