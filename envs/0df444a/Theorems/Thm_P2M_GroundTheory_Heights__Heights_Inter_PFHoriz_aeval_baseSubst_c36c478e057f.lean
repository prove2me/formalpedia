-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:02.295921+00:00
-- url     : https://prove2.me/theorems/316aa70c-4626-459d-ae9b-9e55de048f8b
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFHoriz aeval base Subst c36c478e057f: P2 M Ground Theory Heights  Heights Inter PFHoriz aeval base Subst c36c478e057f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFHoriz aeval base Subst c36c478e057f construction uses the P2 M Ground Theory Heights  Heights Inter PFHoriz aeval base Subst c36c478e057f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L161-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L161-L180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
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
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')

theorem P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFHoriz».«aeval_baseSubst» := P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f
