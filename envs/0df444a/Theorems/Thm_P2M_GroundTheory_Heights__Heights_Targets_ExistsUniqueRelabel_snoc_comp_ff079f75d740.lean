-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_snoc_comp_ff079f75d740
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_snoc_comp_ff079f75d740
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:02.39686+00:00
-- url     : https://prove2.me/theorems/3e260542-5a57-5f75-8f08-274b2ce12198
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel snoc comp ff079f75d740: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel snoc comp ff079f75d740
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel snoc comp ff079f75d740 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel snoc comp ff079f75d740 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L309-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L309-L315

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ
omit hσ
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_snoc_comp_ff079f75d740 {n : ℕ} (L : Fin n → K → ℤ) (A : K → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K → ℤ) L A j ∘ e.symm) =
      Fin.snoc (α := fun _ => K' → ℤ) (fun j => L j ∘ e.symm) (A ∘ e.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«snoc_comp» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_snoc_comp_ff079f75d740
