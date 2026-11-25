-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_of_baseSubst_eq_zero_bce603bba2ac
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mem_of_baseSubst_eq_zero_bce603bba2ac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:33:52.593765+00:00
-- url     : https://prove2.me/theorems/059f095b-d6f7-4ba5-95a7-756e6ee2e147
-- title:
--   P2 M Ground Theory Heights  Heights Inter mem of base Subst eq zero bce603bba2ac: P2 M Ground Theory Heights  Heights Inter mem of base Subst eq zero bce603bba2ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mem of base Subst eq zero bce603bba2ac construction uses the P2 M Ground Theory Heights  Heights Inter mem of base Subst eq zero bce603bba2ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L39-L41

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

theorem P2M_GroundTheory_Heights__Heights_Inter_mem_of_baseSubst_eq_zero_bce603bba2ac (hv : IsBlockMap κ v) (G : GenFibre v P') {f : MRing ι'}
    (hf : baseSubst κ G f = 0) : f ∈ P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mem_of_baseSubst_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_mem_of_baseSubst_eq_zero_bce603bba2ac
