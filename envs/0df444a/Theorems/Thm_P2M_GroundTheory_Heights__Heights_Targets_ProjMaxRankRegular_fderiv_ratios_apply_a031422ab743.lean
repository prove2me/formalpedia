-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:03.546063+00:00
-- url     : https://prove2.me/theorems/21d56b92-9199-5331-85ba-4122180d85df
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Max Rank Regular fderiv ratios apply a031422ab743: P2 M Ground Theory Heights  Heights Targets Proj Max Rank Regular fderiv ratios apply a031422ab743
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Max Rank Regular fderiv ratios apply a031422ab743 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Max Rank Regular fderiv ratios apply a031422ab743 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjMaxRankRegular.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjMaxRankRegular.lean#L14-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRankRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjMaxRankRegular
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
open GroundTheory.Heights₂.Heights.Targets.ProjMaxRankRegular

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {κ τ : Type*}
    [Fintype κ] [Fintype τ] {F : E → κ → ℂ} {u : E} (hF : DifferentiableAt ℂ F u) (a : τ → κ)
    (b : κ) (hb : F u b ≠ 0) (v : E) (t : τ) :
    fderiv ℂ (fun w t => F w (a t) / F w b) u v t =
      (F u b * fderiv ℂ F u v (a t) - F u (a t) * fderiv ℂ F u v b) / F u b ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjMaxRankRegular».«fderiv_ratios_apply» := P2M_GroundTheory_Heights__Heights_Targets_ProjMaxRankRegular_fderiv_ratios_apply_a031422ab743
