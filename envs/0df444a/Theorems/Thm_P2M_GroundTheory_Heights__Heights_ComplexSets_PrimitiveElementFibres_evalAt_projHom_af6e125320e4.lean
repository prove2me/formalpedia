-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_evalAt_projHom_af6e125320e4
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_evalAt_projHom_af6e125320e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:41.26024+00:00
-- url     : https://prove2.me/theorems/4ac594f4-963c-46ea-9df5-b12089cfb797
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres eval At proj Hom af6e125320e4: P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres eval At proj Hom af6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres eval At proj Hom af6e125320e4 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Primitive Element Fibres eval At proj Hom af6e125320e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_evalAt_projHom_af6e125320e4 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {y : Fin d → ℂ} {x : Fin n → ℂ} (hx : x ∈ fibre J A y) (P : MvPolynomial (Fin d) ℂ) :
    evalAt J x hx.1 (projHom J A P) = eval y P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«PrimitiveElementFibres».«evalAt_projHom» := P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_evalAt_projHom_af6e125320e4
