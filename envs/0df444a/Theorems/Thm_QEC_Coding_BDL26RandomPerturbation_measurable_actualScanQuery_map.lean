-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_actualScanQuery_map
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_actualScanQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:13.397932+00:00
-- url     : https://prove2.me/theorems/cecfa846-31a3-4787-9c1c-f9eaade13943
-- title:
--   BDL26 Random Perturbation: measurable actual Scan Query map
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable actual Scan Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L530-L557
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L530-L557

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26RandomPerturbation.measurable_actualScanQuery_map {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w =>
      let R := L.map (fun u => (u, f u w))
      let q := actualScanQuery P (J w) r lambda K (eventUniverseQuery P (J w) hr).1 R
      (q.1.map (eventToMaster P (J w) r), q.2)) := by sorry
