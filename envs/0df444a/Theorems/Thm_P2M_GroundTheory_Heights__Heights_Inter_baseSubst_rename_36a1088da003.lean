-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003
-- name    : P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:12.588637+00:00
-- url     : https://prove2.me/theorems/59aa701c-0265-4cd5-badc-8da101b8545d
-- title:
--   P2 M Ground Theory Heights  Heights Inter base Subst rename 36a1088da003: P2 M Ground Theory Heights  Heights Inter base Subst rename 36a1088da003
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter base Subst rename 36a1088da003 construction uses the P2 M Ground Theory Heights  Heights Inter base Subst rename 36a1088da003 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L18-L32

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

theorem P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003 (hv : IsBlockMap κ v) (G : GenFibre v P') (g : MRing ι) :
    baseSubst κ G (rename v g) = C (aeval G.x g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«baseSubst_rename» := P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003
