-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:45.294053+00:00
-- url     : https://prove2.me/theorems/55c7d004-83c1-465f-8dcb-0e6ab72d813f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk chart Monomial b7a9a7dc5d3e: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk chart Monomial b7a9a7dc5d3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk chart Monomial b7a9a7dc5d3e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point mk chart Monomial b7a9a7dc5d3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L42-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e (i : ∀ k, ι k) (e : K → ℕ) :
    Ideal.Quotient.mk (chartUnitIdeal (F := F) i) (chartMonomial i e) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«mk_chartMonomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mk_chartMonomial_b7a9a7dc5d3e
