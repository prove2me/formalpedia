-- Prove2me | Theorems.Thm_QMCLeafB_Engine_poly_to_certificate
-- name    : QMCLeafB_Engine_poly_to_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T14:40:39.841006+00:00
-- url     : https://prove2.me/theorems/05c0203a-9792-43b2-a230-467d2dd4cdc7
-- title:
--   Engine + Poly o,Rq gives certificate
-- statement:
--   With slack engine and Poly for its bit $o$ and $R_q$, the $W/10000$ certificate exists with $TM_2$.
-- source:
--   QMC leaf B

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

theorem QMCLeafB_Engine_poly_to_certificate
    (eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000))
    (o : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → Bool)
    (hag : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), (match eng G t with | .witness _ _ _ => true | .refuted _ => false) = o ((G, []), t))
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly o)
    (hR : OAI.MetricKMedian.Binary.Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => QuantumMaxCutEnergy.Rq a.1)) :
    ∃ (L : QuantumMaxCutEnergy.Input → ℚ≥0) (X : (G : QuantumMaxCutEnergy.Input) → Matrix (Fin G.n) (Fin G.n) ℝ) (lam : (G : QuantumMaxCutEnergy.Input) → Fin G.n → ℝ), Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest QuantumMaxCutEnergy.encodeValue (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧ ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (QuantumMaxCutEnergy.weightMatrix G) S ∧ ModernConvex.Relaxations.IsUnitDiagPSD (X G) ∧ (QuantumMaxCutEnergy.weightMatrix G + Matrix.diagonal (lam G)).PosSemidef ∧ (L G : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (QuantumMaxCutEnergy.weightMatrix G) (X G) ∧ (1 / 4) * ((∑ i, ∑ j, QuantumMaxCutEnergy.weightMatrix G i j) + ∑ i, lam G i) - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
