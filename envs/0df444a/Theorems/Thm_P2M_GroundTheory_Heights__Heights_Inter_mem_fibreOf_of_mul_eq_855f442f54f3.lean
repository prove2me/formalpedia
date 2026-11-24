-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:13.503794+00:00
-- url     : https://prove2.me/theorems/ff7de883-6c88-4414-8afa-afede4e51a61
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem fibre Of of mul eq 855f442f54f3: P2 M Ground Theory Heights  Heights Inter mem fibre Of of mul eq 855f442f54f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem fibre Of of mul eq 855f442f54f3 construction uses the P2 M Ground Theory Heights  Heights Inter mem fibre Of of mul eq 855f442f54f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L67-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3 (G : GenFibre v P') {I : Ideal (MRing ι')} {c : MRingOver G.Φ (fibreIdx ι' κ)}
    {F : MRing ι'} {g : MRing ι} (hg : aeval G.x g ≠ 0) (e : c * C (aeval G.x g) = baseSubst κ G F) (hF : F ∈ I) :
    c ∈ fibreOf κ G I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_fibreOf_of_mul_eq» := P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3
