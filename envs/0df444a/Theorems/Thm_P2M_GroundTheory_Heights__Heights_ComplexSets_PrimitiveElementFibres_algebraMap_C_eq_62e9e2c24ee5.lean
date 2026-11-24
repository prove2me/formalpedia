-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:40.437932+00:00
-- url     : https://prove2.me/theorems/5ce5854b-0805-40fd-810b-2ebcbdcdec98
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres algebra Map C eq 62e9e2c24ee5: P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres algebra Map C eq 62e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres algebra Map C eq 62e9e2c24ee5 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres algebra Map C eq 62e9e2c24ee5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (a : ℂ) :
    projHom J A (C a) = Ideal.Quotient.mk J (C a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveElementFibres».«algebraMap_C_eq» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_algebraMap_C_eq_62e9e2c24ee5
