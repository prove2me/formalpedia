-- Prove2me | Theorems.Thm_QMCLeafB_Engine_to_certificate_program
-- name    : QMCLeafB_Engine_to_certificate_program
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T16:10:12.035205+00:00
-- url     : https://prove2.me/theorems/f2103d59-d016-4370-bd7f-1b9d6bb6cf82
-- title:
--   Slack engine gives certificate program (with X and lambda)
-- statement:
--   A slack engine with tolerances $1/40000$ yields $L(G), X(G), \lambda(G)$ with $L(G)\le$ primal objective and duality gap $\le W/10000$, and $L$ is $TM_2$-computable. This is the certificate form of the leaf.
-- source:
--   QMC leaf B, engine to certificate

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer

open scoped BigOperators

theorem QMCLeafB_Engine_to_certificate_program
    (eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000)) :
    ∃ (L : QuantumMaxCutEnergy.Input → ℚ≥0) (X : (G : QuantumMaxCutEnergy.Input) → Matrix (Fin G.n) (Fin G.n) ℝ) (lam : (G : QuantumMaxCutEnergy.Input) → Fin G.n → ℝ), Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧ ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (QuantumMaxCutEnergy.weightMatrix G) S ∧ ModernConvex.Relaxations.IsUnitDiagPSD (X G) ∧ (QuantumMaxCutEnergy.weightMatrix G + Matrix.diagonal (lam G)).PosSemidef ∧ (L G : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QuantumMaxCutEnergy.weightMatrix G) (X G) ∧ (1 / 4) * ((∑ i, ∑ j, QuantumMaxCutEnergy.weightMatrix G i j) + ∑ i, lam G i) - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
