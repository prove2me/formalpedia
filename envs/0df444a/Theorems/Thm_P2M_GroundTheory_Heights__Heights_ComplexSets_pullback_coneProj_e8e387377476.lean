-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:07.879778+00:00
-- url     : https://prove2.me/theorems/185102e0-3145-463c-a042-dfcff2393d1c
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets pullback cone Proj e8e387377476: P2 M Ground Theory Heights  Heights Complex Sets pullback cone Proj e8e387377476
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets pullback cone Proj e8e387377476 construction uses the P2 M Ground Theory Heights  Heights Complex Sets pullback cone Proj e8e387377476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L246-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L246-L257

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476 (P : MvPolynomial (Fin 2) ℂ) :
    finSuccEquiv ℂ 2 (pullback coneProj P) = Polynomial.C P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«pullback_coneProj» := P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_coneProj_e8e387377476
