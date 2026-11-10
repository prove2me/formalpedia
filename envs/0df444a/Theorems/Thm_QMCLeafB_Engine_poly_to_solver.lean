-- Prove2me | Theorems.Thm_QMCLeafB_Engine_poly_to_solver
-- name    : QMCLeafB_Engine_poly_to_solver
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T14:41:27.265366+00:00
-- url     : https://prove2.me/theorems/54f66802-200c-48f9-b043-56c6b82544f0
-- title:
--   Engine + Poly gives Poly solver (v2)
-- statement:
--   With slack engine and Poly bit and $R_q$, the Poly solver with gap $W/10000$ exists.
-- source:
--   QMC leaf B, engine to solver

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer
import Definitions.Def_QMCLeafB_Rq
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

instance instCodingInputListBool : Coding (QuantumMaxCutEnergy.Input × List Bool) := ⟨QuantumMaxCutEnergy.encodeRequest⟩

theorem QMCLeafB_Engine_poly_to_solver
    (eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000))
    (o : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → Bool)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), (match eng G t with | .witness _ _ _ => true | .refuted _ => false) = o ((G, []), t))
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly o)
    (hR : OAI.MetricKMedian.Binary.Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => QuantumMaxCutEnergy.Rq a.1)) :
    ∃ Solve : List QMCNumericRuntime.NumericEdge → List (List ℚ) × List ℚ, OAI.MetricKMedian.Binary.Automatic.Poly Solve ∧ ∀ G : QuantumMaxCutEnergy.Input, ModernConvex.Relaxations.IsUnitDiagPSD (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ∧ (Matrix.diagonal (fun i : Fin G.n => (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ)) + (1 / 4 : ℝ) • (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧ (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) + ∑ i : Fin G.n, (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ) - ModernConvex.Relaxations.maxcutRelaxationObjective (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
