-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_isMultiHomog_30eea56ab449
-- name    : P2M_GroundTheory_Heights__Heights_Inter_baseSubst_isMultiHomog_30eea56ab449
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:33.339845+00:00
-- url     : https://prove2.me/theorems/4b77e723-c2fb-4a67-bdf8-de49aaeb6188
-- title:
--   P2 M Ground Theory Heights  Heights Inter base Subst is Multi Homog 30eea56ab449: P2 M Ground Theory Heights  Heights Inter base Subst is Multi Homog 30eea56ab449
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter base Subst is Multi Homog 30eea56ab449 construction uses the P2 M Ground Theory Heights  Heights Inter base Subst is Multi Homog 30eea56ab449 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L63-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreSum.lean#L63-L98

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

theorem P2M_GroundTheory_Heights__Heights_Inter_baseSubst_isMultiHomog_30eea56ab449 (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«baseSubst_isMultiHomog» := P2M_GroundTheory_Heights__Heights_Inter_baseSubst_isMultiHomog_30eea56ab449
