-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:18.942438+00:00
-- url     : https://prove2.me/theorems/25374c10-a4c7-4d0e-955d-b4df1d4fcb67
-- title:
--   P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum sheet Sum 5ea7d9e12fbf: P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum sheet Sum 5ea7d9e12fbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum sheet Sum 5ea7d9e12fbf construction uses the P2 M Ground Theory Heights  Heights Chart Int Count Add has Sum sheet Sum 5ea7d9e12fbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PChartIntCountAdd.lean#L45-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntCountAdd».«hasSum_sheetSum» := P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf
