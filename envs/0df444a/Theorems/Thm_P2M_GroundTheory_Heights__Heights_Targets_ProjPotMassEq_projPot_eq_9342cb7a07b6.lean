-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:20.072983+00:00
-- url     : https://prove2.me/theorems/d152e772-33b0-5573-a0c7-42c456d6e91c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proj Pot eq 9342cb7a07b6: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proj Pot eq 9342cb7a07b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proj Pot eq 9342cb7a07b6 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq proj Pot eq 9342cb7a07b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L34-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEq.lean#L34-L63

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6 (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (b z : V)
    (hzb : z.1 ∈ R.U b.1) (hz : Ψ (segre (R.lift z.1 z.1)) ≠ 0) :
    (projPot R Ψ V).φ b z = (multiprojPot R V).φ b z + uFun R Ψ V z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«projPot_eq» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_projPot_eq_9342cb7a07b6
