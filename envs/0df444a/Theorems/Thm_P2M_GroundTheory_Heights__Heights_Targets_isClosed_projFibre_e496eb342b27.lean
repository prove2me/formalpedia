-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27
-- name    : P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:52.397099+00:00
-- url     : https://prove2.me/theorems/38e4afe1-028e-5932-99c2-1b40f7743425
-- title:
--   P2 M Ground Theory Heights  Heights Targets is Closed proj Fibre e496eb342b27: P2 M Ground Theory Heights  Heights Targets is Closed proj Fibre e496eb342b27
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets is Closed proj Fibre e496eb342b27 construction uses the P2 M Ground Theory Heights  Heights Targets is Closed proj Fibre e496eb342b27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L39-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularFibre.lean#L39-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularFibre
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27 {n : ℕ} (R : AnLogRes P J (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (hV : IsClosed V)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) (y : Fin n → ℂ) :
    IsClosed {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«isClosed_projFibre» := P2M_GroundTheory_Heights__Heights_Targets_isClosed_projFibre_e496eb342b27
