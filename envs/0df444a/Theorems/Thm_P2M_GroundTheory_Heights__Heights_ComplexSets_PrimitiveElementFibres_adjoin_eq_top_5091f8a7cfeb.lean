-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:33.362799+00:00
-- url     : https://prove2.me/theorems/5bf7304c-4867-4aaf-9646-aa62cd94ad89
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres adjoin eq top 5091f8a7cfeb: P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres adjoin eq top 5091f8a7cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres adjoin eq top 5091f8a7cfeb construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres adjoin eq top 5091f8a7cfeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L23-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveElementFibres».«adjoin_eq_top» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_adjoin_eq_top_5091f8a7cfeb
