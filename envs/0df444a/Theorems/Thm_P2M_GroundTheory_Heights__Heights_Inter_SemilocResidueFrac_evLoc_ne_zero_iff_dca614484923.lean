-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_ne_zero_iff_dca614484923
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_ne_zero_iff_dca614484923
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:50.913642+00:00
-- url     : https://prove2.me/theorems/b3f5c0c1-244a-4840-9582-881ff6b3ad73
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc ne zero iff dca614484923: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc ne zero iff dca614484923
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc ne zero iff dca614484923 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc ne zero iff dca614484923 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L92-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_ne_zero_iff_dca614484923 (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} :
    evLoc P W hPW x hx z ≠ 0 ↔ IsUnit z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«evLoc_ne_zero_iff» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_ne_zero_iff_dca614484923
