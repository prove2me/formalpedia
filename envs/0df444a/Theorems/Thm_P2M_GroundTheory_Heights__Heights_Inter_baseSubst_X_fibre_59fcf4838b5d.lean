-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:55.033615+00:00
-- url     : https://prove2.me/theorems/3e392624-e90c-4dfb-9e79-4dcd5e154b82
-- title:
--   P2 M Ground Theory Heights  Heights Inter base Subst X fibre 59fcf4838b5d: P2 M Ground Theory Heights  Heights Inter base Subst X fibre 59fcf4838b5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter base Subst X fibre 59fcf4838b5d construction uses the P2 M Ground Theory Heights  Heights Inter base Subst X fibre 59fcf4838b5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L34-L37

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

theorem P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«baseSubst_X_fibre» := P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d
