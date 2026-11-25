-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:34.257418+00:00
-- url     : https://prove2.me/theorems/20fda3c8-bcba-497b-9fc2-ea42353542d5
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFHoriz fibre Ideal gen Fibre Of 3eecdf1a8d31: P2 M Ground Theory Heights  Heights Inter PFHoriz fibre Ideal gen Fibre Of 3eecdf1a8d31
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFHoriz fibre Ideal gen Fibre Of 3eecdf1a8d31 construction uses the P2 M Ground Theory Heights  Heights Inter PFHoriz fibre Ideal gen Fibre Of 3eecdf1a8d31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L182-L187

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31 (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFHoriz».«fibreIdeal_genFibreOf» := P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31
