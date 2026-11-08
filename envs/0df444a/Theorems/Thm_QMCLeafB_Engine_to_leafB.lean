-- Prove2me | Theorems.Thm_QMCLeafB_Engine_to_leafB
-- name    : QMCLeafB_Engine_to_leafB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T16:08:22.404562+00:00
-- url     : https://prove2.me/theorems/08e77886-ee0a-4e7b-a235-bbc85cfec20d
-- title:
--   Slack engine gives W/10000 approximation (no Poly)
-- statement:
--   A slack engine $eng(G,t)$ with tolerances $1/40000$ gives a rational $L(G)$ with $L(G)\le S(G)\le L(G)+W/10000$ where $S(G)$ is the Max-Cut SDP value and $W$ total weight. This is the analytic half of the leaf, without computability.
-- source:
--   QMC leaf B, engine to sandwich

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergy_weightMatrix
import Definitions.Def_QMCLeafB_AnswerProducer

open scoped BigOperators

theorem QMCLeafB_Engine_to_leafB
    (eng : (G : QuantumMaxCutEnergy.Input) → ∀ t : ℚ, QMCLeafB.AnswerProducer.Answerε (QuantumMaxCutEnergy.weightMatrix G) t (1/40000) (1/40000)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (QuantumMaxCutEnergy.weightMatrix G) S ∧ (L G : ℝ) ≤ S ∧ S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by sorry
