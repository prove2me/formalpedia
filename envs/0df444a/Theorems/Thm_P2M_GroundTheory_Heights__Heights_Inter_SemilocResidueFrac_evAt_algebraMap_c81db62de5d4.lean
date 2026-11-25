-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evAt_algebraMap_c81db62de5d4
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evAt_algebraMap_c81db62de5d4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:46.001141+00:00
-- url     : https://prove2.me/theorems/91d4daeb-42ae-520f-a1bc-c750cf20a4f1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev At algebra Map c81db62de5d4: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev At algebra Map c81db62de5d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev At algebra Map c81db62de5d4 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev At algebra Map c81db62de5d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L54-L57

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evAt_algebraMap_c81db62de5d4 (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) (f : MRing ι) :
    evAt P W hPW x hx (algebraMap _ _ (Ideal.Quotient.mk P f)) = aeval x f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«evAt_algebraMap» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evAt_algebraMap_c81db62de5d4
