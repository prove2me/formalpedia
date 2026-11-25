-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:42.114806+00:00
-- url     : https://prove2.me/theorems/42c86fb8-058b-4ec5-98fd-235ff1c40546
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc spec e16d5efc3bff: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc spec e16d5efc3bff
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc spec e16d5efc3bff construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac ev Loc spec e16d5efc3bff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L74-L82

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} {u w : MRing ι}
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) :
    evLoc P W hPW x hx z * aeval x w = aeval x u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«evLoc_spec» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff
