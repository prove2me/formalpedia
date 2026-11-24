-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:24.861788+00:00
-- url     : https://prove2.me/theorems/ff4d3af0-9526-4c4e-b117-a760ae62d944
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rhs R equiv ab54d4a8ce7e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rhs R equiv ab54d4a8ce7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rhs R equiv ab54d4a8ce7e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rhs R equiv ab54d4a8ce7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsExtraBis.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsExtraBis.lean#L13-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι)
    (A : HermLine ι) (s : MRing ι) : rhsR I P L A s = recR I P L A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«rhsR».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e
