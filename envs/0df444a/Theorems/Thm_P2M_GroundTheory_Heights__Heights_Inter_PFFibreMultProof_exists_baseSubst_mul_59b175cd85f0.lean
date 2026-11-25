-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:18.035853+00:00
-- url     : https://prove2.me/theorems/eb077481-2dc4-45f7-a39d-58101525f1db
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists base Subst mul 59b175cd85f0: P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists base Subst mul 59b175cd85f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists base Subst mul 59b175cd85f0 construction uses the P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists base Subst mul 59b175cd85f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L59-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0 (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (t : MRing ι) (f : MRing ι'), aeval G.x t ≠ 0 ∧ baseSubst κ G (rename v t) * g = baseSubst κ G f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFFibreMultProof».«exists_baseSubst_mul» := P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
