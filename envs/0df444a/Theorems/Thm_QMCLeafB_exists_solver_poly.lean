-- Prove2me | Theorems.Thm_QMCLeafB_exists_solver_poly
-- name    : QMCLeafB_exists_solver_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T14:55:24.586643+00:00
-- url     : https://prove2.me/theorems/855885f4-bf86-47f7-bc89-6fdf48e521d6
-- title:
--   Solver Poly exists unconditional
-- statement:
--   There exists a $Poly$ solver $Solve$ with gap $W/10000$ unconditionally.
-- source:
--   QMC leaf B unconditional solver

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open scoped BigOperators

theorem QMCLeafB_exists_solver_poly : ∃ Solve : List QMCNumericRuntime.NumericEdge → List (List ℚ) × List ℚ, OAI.MetricKMedian.Binary.Automatic.Poly Solve ∧ ∀ G : QuantumMaxCutEnergy.Input, ModernConvex.Relaxations.IsUnitDiagPSD (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ∧ (Matrix.diagonal (fun i : Fin G.n => (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ)) + (1 / 4 : ℝ) • (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧ (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) + ∑ i : Fin G.n, (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ) - ModernConvex.Relaxations.maxcutRelaxationObjective (Matrix.of fun i j : Fin G.n => if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) (Matrix.of fun i j : Fin G.n => ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
