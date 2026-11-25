-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365
-- name    : P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:33.399577+00:00
-- url     : https://prove2.me/theorems/fece4e32-0999-4dd6-9b33-0b11b07401c2
-- title:
--   P2 M Ground Theory Heights  Heights Chart Residue Degree ratio 23e579f45365: P2 M Ground Theory Heights  Heights Chart Residue Degree ratio 23e579f45365
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Residue Degree ratio 23e579f45365 construction uses the P2 M Ground Theory Heights  Heights Chart Residue Degree ratio 23e579f45365 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L97-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L97-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartResidueDegree

theorem P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365 {K σ : Type*} [Field K] {n : ℕ} (ξ τ : Fin n → K) (A : Fin n → MvPolynomial σ K)
    (B : MvPolynomial σ K) (ℓ' : K) (hB : B ≠ 0) (hℓ : ∑ l, τ l * ξ l ≠ 0)
    (hrel : ∀ m, A m * C ℓ' = B * C (ξ m)) :
    ∑ l, C (τ l) * A l ≠ 0 ∧ ∀ m, A m = C (ξ m / ∑ l, τ l * ξ l) * ∑ l, C (τ l) * A l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartResidueDegree».«ratio» := P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365
