-- Prove2me | Theorems.Thm_QMCLeafB_Engine_to_solver_poly
-- name    : QMCLeafB_Engine_to_solver_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T16:12:56.23692+00:00
-- url     : https://prove2.me/theorems/1602556d-f080-454f-9247-d69502ad097e
-- title:
--   Slack engine gives Poly solver for Max-Cut SDP
-- statement:
--   A slack engine yields a $Poly$ solver $Solve$ that on $inputEdges(G)$ returns rational primal $X$ and dual $\lambda$ with $X\succeq0$, $X_{ii}=1$, $A(G)+diag(\lambda)\succeq0$ and gap $\le W/10000$. This is the $Poly$ refinement of the certificate.
-- source:
--   QMC leaf B, engine to solver

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer

open scoped BigOperators

theorem QMCLeafB_Engine_to_solver_poly
    (eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000)) :
    ∃ Solve : List QMCNumericRuntime.NumericEdge → List (List ℚ) × List ℚ,
      OAI.MetricKMedian.Binary.Automatic.Poly Solve ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        ModernConvex.Relaxations.IsUnitDiagPSD
          (Matrix.of fun i j : Fin G.n =>
            ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ)) ∧
        (Matrix.diagonal (fun i : Fin G.n =>
            (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ)) +
          (1 / 4 : ℝ) • (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧
        (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) +
          ∑ i : Fin G.n, (((Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0 : ℚ) : ℝ) -
          ModernConvex.Relaxations.maxcutRelaxationObjective
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
            (Matrix.of fun i j : Fin G.n =>
              ((((Solve (QMCNumericRuntime.inputEdges G)).1[i.val]?.getD [])[j.val]?.getD 0 : ℚ) : ℝ))
          ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
