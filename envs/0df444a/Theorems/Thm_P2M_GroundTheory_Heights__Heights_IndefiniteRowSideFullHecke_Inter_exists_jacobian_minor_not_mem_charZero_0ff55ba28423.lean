-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_jacobian_minor_not_mem_charZero_0ff55ba28423
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_jacobian_minor_not_mem_charZero_0ff55ba28423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:28.593747+00:00
-- url     : https://prove2.me/theorems/5f907b3d-e68f-4b5c-93eb-739f444dd2ec
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists jacobian minor not mem char Zero 0ff55ba28423: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists jacobian minor not mem char Zero 0ff55ba28423 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists jacobian minor not mem char Zero 0ff55ba28423 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/JacMinorC.lean#L44-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/JacMinorC.lean#L44-L233

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_jacobian_minor_not_mem_charZero_0ff55ba28423 {F : Type} [Field F] [CharZero F] {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ F) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ F ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_jacobian_minor_not_mem_charZero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_jacobian_minor_not_mem_charZero_0ff55ba28423
