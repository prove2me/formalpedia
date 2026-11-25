-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:05:17.31445+00:00
-- url     : https://prove2.me/theorems/b49c698e-1dd9-521c-a972-af6fdf45bf2e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq block Sum pos f3a6ed830dc6: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq block Sum pos f3a6ed830dc6
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq block Sum pos f3a6ed830dc6 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq block Sum pos f3a6ed830dc6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«blockSum_pos» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
