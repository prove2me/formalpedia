-- Prove2me | Theorems.Thm_QMCLeafB_Rq_poly
-- name    : QMCLeafB_Rq_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-09T14:42:17.041768+00:00
-- url     : https://prove2.me/theorems/eb39c95e-8af3-41e9-a2ec-8229340a10ee
-- title:
--   Rq is Poly
-- statement:
--   $R_q(G)=2\sum_e w_e$ is $Poly$ in $encodeRequest$.
-- source:
--   QMC leaf B, rq-program

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QMCLeafB_Rq

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

instance instCodingInputListBool : Coding (QuantumMaxCutEnergy.Input × List Bool) := ⟨QuantumMaxCutEnergy.encodeRequest⟩

theorem QMCLeafB_Rq_poly : OAI.MetricKMedian.Binary.Automatic.Poly (fun a : QuantumMaxCutEnergy.Input × List Bool => QuantumMaxCutEnergy.Rq a.1) := by sorry
