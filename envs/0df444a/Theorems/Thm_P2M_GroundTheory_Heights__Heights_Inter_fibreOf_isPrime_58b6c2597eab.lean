-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fibreOf_isPrime_58b6c2597eab
-- name    : P2M_GroundTheory_Heights__Heights_Inter_fibreOf_isPrime_58b6c2597eab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:44.28148+00:00
-- url     : https://prove2.me/theorems/f300c2f5-1847-504e-bd95-9bc0f7ab1526
-- title:
--   P2 M Ground Theory Heights  Heights Inter fibre Of is Prime 58b6c2597eab: P2 M Ground Theory Heights  Heights Inter fibre Of is Prime 58b6c2597eab
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter fibre Of is Prime 58b6c2597eab construction uses the P2 M Ground Theory Heights  Heights Inter fibre Of is Prime 58b6c2597eab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L121-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L121-L136

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

theorem P2M_GroundTheory_Heights__Heights_Inter_fibreOf_isPrime_58b6c2597eab (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«fibreOf_isPrime» := P2M_GroundTheory_Heights__Heights_Inter_fibreOf_isPrime_58b6c2597eab
