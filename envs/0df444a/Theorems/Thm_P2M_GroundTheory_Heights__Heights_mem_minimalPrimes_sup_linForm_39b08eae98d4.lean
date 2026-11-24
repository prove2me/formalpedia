-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4
-- name    : P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:55.449087+00:00
-- url     : https://prove2.me/theorems/14c233f1-ac15-44d6-bbe0-d7add256aac7
-- title:
--   P2 M Ground Theory Heights  Heights mem minimal Primes sup lin Form 39b08eae98d4: P2 M Ground Theory Heights  Heights mem minimal Primes sup lin Form 39b08eae98d4
-- statement:
--   The P2 M Ground Theory Heights  Heights mem minimal Primes sup lin Form 39b08eae98d4 construction uses the P2 M Ground Theory Heights  Heights mem minimal Primes sup lin Form 39b08eae98d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOnZero.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitOnZero.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitGoodPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalLimitGlueOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4 {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} (hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_minimalPrimes_sup_linForm» := P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_sup_linForm_39b08eae98d4
