-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:42:34.619901+00:00
-- url     : https://prove2.me/theorems/9f85ff79-b7cf-41ae-aba1-82b941f06560
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFHoriz base Subst rename cb9c3ab4b8a4: P2 M Ground Theory Heights  Heights Inter PFHoriz base Subst rename cb9c3ab4b8a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFHoriz base Subst rename cb9c3ab4b8a4 construction uses the P2 M Ground Theory Heights  Heights Inter PFHoriz base Subst rename cb9c3ab4b8a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L105-L118

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4 (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFHoriz».«baseSubst_rename» := P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4
