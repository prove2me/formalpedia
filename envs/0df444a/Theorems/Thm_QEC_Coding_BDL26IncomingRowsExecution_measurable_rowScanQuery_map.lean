-- Prove2me | Theorems.Thm_QEC_Coding_BDL26IncomingRowsExecution_measurable_rowScanQuery_map
-- name    : QEC.Coding.BDL26IncomingRowsExecution.measurable_rowScanQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:24:34.003144+00:00
-- url     : https://prove2.me/theorems/e70a3b15-a221-4290-a6e1-8c4b825e3f8f
-- title:
--   BDL26 Incoming Rows Execution: measurable row Scan Query map
-- statement:
--   The BDL26 Incoming Rows Execution construction uses the measurable row Scan Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L971-L999
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/IncomingRowsExecution.lean#L971-L999

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26IncomingRowsExecution
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] BDL26RandomPerturbation.countedLabelListMeasurable
  BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26IncomingRowsExecution.measurable_rowScanQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ v, Measurable (f v)) :
    Measurable (fun w =>
      let I := incomingRows P (J w)
      let R := L.map (fun v => (v,f v w))
      let q := rowScanQuery P I r lambda K (rowUniverseQuery P I hr).1 R
      (q.1.map (eventToMaster P (statePoints I) r),q.2)) := by sorry
