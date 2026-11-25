-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:04.850878+00:00
-- url     : https://prove2.me/theorems/6c9c1a67-2322-4b70-a240-387c0893f52c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rec R family eq 65fe609818ce: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rec R family eq 65fe6098
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rec R family eq 65fe609818ce construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rec R family eq 65fe609818ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L65-L76

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    (I J : Family ι) :
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR J P Fin.elim0 A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«recR_family_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce
