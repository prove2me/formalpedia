-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_rangeSubfield_256513a2046f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_rangeSubfield_256513a2046f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:30.265955+00:00
-- url     : https://prove2.me/theorems/a955f409-8357-427f-a179-a329ffaf7136
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem range Subfield 256513a2046f: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem range Subfield 256513a2046f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem range Subfield 256513a2046f construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem range Subfield 256513a2046f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L132-L134

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
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_rangeSubfield_256513a2046f {R : Type*} [CommRing R] (ρ : R →+* Ω) (hinv : ∀ r, ρ r ≠ 0 → ∃ r', ρ r' * ρ r = 1)
    (r : R) : ρ r ∈ rangeSubfield ρ hinv := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«mem_rangeSubfield» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_rangeSubfield_256513a2046f
