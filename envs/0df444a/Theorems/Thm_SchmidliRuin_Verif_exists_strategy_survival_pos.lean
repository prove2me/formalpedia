-- Prove2me | Theorems.Thm_SchmidliRuin_Verif_exists_strategy_survival_pos
-- name    : SchmidliRuin.Verif.exists_strategy_survival_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:23.452286+00:00
-- url     : https://prove2.me/theorems/46339cbc-2c2d-4fed-be87-7bd1a8cd3b1f
-- title:
--   §3, proof of Theorem 1, p. 897 — there is an admissible strategy with ℙ[τ = ∞] > 0
-- statement:
--   Assume the model of §1 and the standing assumptions. For every initial capital $u\ge0$ there is an admissible strategy $(A,b)$ from $u$ whose surplus process $X$ survives with positive probability:
--   $$\mathbb P[\tau=\infty]>0 .$$
--
--   The verification theorem uses this to conclude that $f(\infty)<\infty$. It also shows that the supremum defining the value function $\delta(u)$ is taken over a nonempty set.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), p. 897, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_SchmidliRuin_Verif_Setting
import Definitions.Def_SchmidliRuin_Verif_Model

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

theorem exists_strategy_survival_pos {Ω : Type*} [MeasurableSpace Ω] (B : RiskBasis Ω)
    (hB : B.IsValid) (c mu sigma : ℝ) (hc : 0 < c) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (cb : ℝ → ℝ) (hcb : ReinsPremium c cb) (u : ℝ) (hu : 0 ≤ u) :
    ∃ A b X : ℝ≥0 → Ω → ℝ, IsAdmissible B c mu sigma cb u A b X ∧
      0 < B.P {ω | survives X ω} := by sorry

end SchmidliRuin.Verif
