-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pderiv_facts_charZero_b7d4ab5b97c4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pderiv_facts_charZero_b7d4ab5b97c4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:35.353957+00:00
-- url     : https://prove2.me/theorems/f7d03cc4-3da5-469b-b2b9-c4506e3f3fac
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pderiv facts char Zero b7d4ab5b97c4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pderiv facts char
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pderiv facts char Zero b7d4ab5b97c4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pderiv facts char Zero b7d4ab5b97c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/JacMinorC.lean#L11-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/JacMinorC.lean#L11-L42

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pderiv_facts_charZero_b7d4ab5b97c4 {F : Type*} [Field F] [CharZero F] {σ : Type*} (p : MvPolynomial σ F) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pderiv_facts_charZero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pderiv_facts_charZero_b7d4ab5b97c4
