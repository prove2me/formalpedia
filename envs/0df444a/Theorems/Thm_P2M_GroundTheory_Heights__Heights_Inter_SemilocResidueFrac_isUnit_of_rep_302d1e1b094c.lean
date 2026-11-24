-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:35.528849+00:00
-- url     : https://prove2.me/theorems/05a37b7a-d311-4862-a869-51ac73b7ef20
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac is Unit of rep 302d1e1b094c: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac is Unit of rep 302d1e1b094c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac is Unit of rep 302d1e1b094c construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac is Unit of rep 302d1e1b094c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L84-L90

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c (P W : Ideal (MRing ι)) [P.IsPrime] (hPW : P ≤ W) {z : locRing P W} {u w : MRing ι}
    {a : K → ℕ} (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) (huW : u ∉ W)
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) : IsUnit z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«isUnit_of_rep» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c
