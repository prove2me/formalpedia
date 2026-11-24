-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:11.800855+00:00
-- url     : https://prove2.me/theorems/dc8aa3be-0155-4992-91d2-43ce7567b054
-- title:
--   P2 M Ground Theory Heights  Heights Inter aeval base Subst c8867875a98c: P2 M Ground Theory Heights  Heights Inter aeval base Subst c8867875a98c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter aeval base Subst c8867875a98c construction uses the P2 M Ground Theory Heights  Heights Inter aeval base Subst c8867875a98c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
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
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«aeval_baseSubst» := P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c
