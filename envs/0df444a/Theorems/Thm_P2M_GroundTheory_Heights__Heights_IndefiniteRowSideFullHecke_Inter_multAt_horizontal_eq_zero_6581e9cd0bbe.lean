-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:10.574875+00:00
-- url     : https://prove2.me/theorems/6002d5de-6d9b-4e00-a5b6-78acd466b505
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At horizontal eq zero 6581e9cd0bbe: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At horiz
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At horizontal eq zero 6581e9cd0bbe construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter mult At horizontal eq zero 6581e9cd0bbe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L32-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L32-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    {W₀ : Ideal (MRing ι)} (hW₀ : W₀ ∈ divSupp P s) (hh : IsHorizontal W₀) :
    (multAt (P ⊔ Ideal.span {s}) W₀ : ℝ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«multAt_horizontal_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe
