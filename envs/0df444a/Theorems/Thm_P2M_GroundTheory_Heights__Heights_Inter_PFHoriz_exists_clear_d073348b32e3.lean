-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:40.170416+00:00
-- url     : https://prove2.me/theorems/d5078f93-6b8b-5f5a-a95a-82963d0399fd
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFHoriz exists clear d073348b32e3: P2 M Ground Theory Heights  Heights Inter PFHoriz exists clear d073348b32e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFHoriz exists clear d073348b32e3 construction uses the P2 M Ground Theory Heights  Heights Inter PFHoriz exists clear d073348b32e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L120-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFHoriz.lean#L120-L138

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3 (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFHoriz».«exists_clear» := P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3
