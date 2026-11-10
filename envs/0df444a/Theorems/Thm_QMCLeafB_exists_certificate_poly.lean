-- Prove2me | Theorems.Thm_QMCLeafB_exists_certificate_poly
-- name    : QMCLeafB_exists_certificate_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T14:53:36.912223+00:00
-- url     : https://prove2.me/theorems/0fd82e06-a6f9-40b8-a5d5-2eae9c8c6e10
-- title:
--   Certificate exists with Poly (unconditional)
-- statement:
--   There exist $L,X,\lambda$ with $TM_2$ and gap $W/10000$ unconditionally (ellipsoid construction).
-- source:
--   QMC leaf B unconditional

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer
import Definitions.Def_QMCLeafB_Rq

open scoped BigOperators

theorem QMCLeafB_exists_certificate_poly : ∃ (L : QuantumMaxCutEnergy.Input → ℚ≥0) (X : (G : QuantumMaxCutEnergy.Input) → Matrix (Fin G.n) (Fin G.n) ℝ) (lam : (G : QuantumMaxCutEnergy.Input) → Fin G.n → ℝ), Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧ ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (QuantumMaxCutEnergy.weightMatrix G) S ∧ ModernConvex.Relaxations.IsUnitDiagPSD (X G) ∧ (QuantumMaxCutEnergy.weightMatrix G + Matrix.diagonal (lam G)).PosSemidef ∧ (L G : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QuantumMaxCutEnergy.weightMatrix G) (X G) ∧ (1 / 4) * ((∑ i, ∑ j, QuantumMaxCutEnergy.weightMatrix G i j) + ∑ i, lam G i) - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
