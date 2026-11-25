-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:50.664903+00:00
-- url     : https://prove2.me/theorems/dd7193d6-60d5-429f-a47a-f6ed8c74a882
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover chart rel f6b2a434feeb: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover chart rel f6b2a434feeb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover chart rel f6b2a434feeb construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover chart rel f6b2a434feeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L151-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L151-L218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) {κ ν : Type} [Fintype κ]
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω)
    (hgen : ∀ ψ ∈ T.dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing ℤ x i) ∧ ψ = ∑ k, c k • (x i)⁻¹ • φ k)
    (hdet : ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      T.detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l))
    {f : Ω} (hf : f ∈ chartRing ℤ x i) (bb : Fin 2 → E) (hli : LinearIndependent Ω bb)
    (hsp : Submodule.span Ω (Set.range bb) = ⊤) (hgenb : ∀ q, ∃ n : ℕ, f ^ n • bb q ∈ B.lat i) (M : ℕ)
    (hM : ∀ v ∈ B.lat i, ∀ q, f ^ M * (Module.Basis.mk hli hsp.ge).repr v q ∈ chartRing ℤ x i) :
    ∃ n : ℕ, f ^ n ∈ Submodule.span (chartRing ℤ x i) (Set.range fun t : κ × κ × ν =>
      (x i)⁻¹ ^ 3 * (φ t.1 (e 0) * φ t.2.1 (e 1) - φ t.1 (e 1) * φ t.2.1 (e 0)) * δ t.2.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«chart_rel» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb
