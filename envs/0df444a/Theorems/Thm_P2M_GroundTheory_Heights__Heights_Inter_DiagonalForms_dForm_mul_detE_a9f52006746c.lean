-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:16.162809+00:00
-- url     : https://prove2.me/theorems/f77afca5-53a6-4ed0-96be-ad1182ad1abd
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form mul det E a9f52006746c: P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form mul det E a9f52006746c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form mul det E a9f52006746c construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form mul det E a9f52006746c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L173-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L173-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * T.detE e u w = ψ u * ψ' w - ψ w * ψ' u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«dForm_mul_detE» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_mul_detE_a9f52006746c
