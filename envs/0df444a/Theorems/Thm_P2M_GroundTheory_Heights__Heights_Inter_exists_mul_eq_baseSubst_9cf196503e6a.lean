-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:00.118093+00:00
-- url     : https://prove2.me/theorems/055604e1-6f37-4670-9d4f-f6fccf1b0c67
-- title:
--   P2 M Ground Theory Heights  Heights Inter exists mul eq base Subst 9cf196503e6a: P2 M Ground Theory Heights  Heights Inter exists mul eq base Subst 9cf196503e6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter exists mul eq base Subst 9cf196503e6a construction uses the P2 M Ground Theory Heights  Heights Inter exists mul eq base Subst 9cf196503e6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L47-L65

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

theorem P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a (hv : IsBlockMap κ v) (G : GenFibre v P') (c : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (F : MRing ι') (g : MRing ι), aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«exists_mul_eq_baseSubst» := P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
