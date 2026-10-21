-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_5
-- name    : SWSSNet.Diffusion.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:55.38011+00:00
-- url     : https://prove2.me/theorems/d0c8cb26-28f3-4141-bd1f-96b082d54050
-- title:
--   Theorem 5 — ϑ_p < 0: transient under every stationary Markov control; ϑ_p = 0: no invariant probability measure
-- statement:
--   Let $p$ be a positive probability vector and $\vartheta_p$ the SWSS parameter. Consider the limiting diffusion (41) with drift (42) and $h$ given by (12), under a stationary Markov control $U_t=v(X_t)$, where $v:\mathbb R^I\to\Delta_I\times\Delta_J$ is any Borel map.
--
--   1. If $\vartheta_p<0$, then the diffusion is **transient** under every such control: every strong solution, from every initial point, satisfies $|X_t|\to\infty$ almost surely.
--   2. If $\vartheta_p=0$, then under every such control the transition probability of the strong solutions has no invariant probability measure. In particular, the diffusion is not positive recurrent.
--
--   This is the instability half of the stability dichotomy of Theorem 1. A negative safety staffing cannot be compensated by any scheduling of the limiting diffusion.
--
--   **Formalization Note** "Cannot be positive recurrent" is rendered as the absence of an invariant probability measure for the transition law of the strong solutions, as in Theorem 1's parenthesis. Strong solutions exist and are pathwise unique for every Borel control, because the drift is locally bounded with linear growth and the noise is nondegenerate and additive. This is background, not part of the statement.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 22, Theorem 5

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Theorem 5, p. 22: if `ϑ_p < 0`, the limiting diffusion (41) is transient under every stationary
Markov control; if `ϑ_p = 0`, under every stationary Markov control it has no invariant probability
measure. -/
theorem theorem_5 {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    (swss N p < 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      IsTransient (markovDrift N (hvec N) v) (Sigma N)) ∧
    (swss N p = 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) v) (Sigma N) P →
        ¬ ∃ π, GPhNGIDiffusion.EMError.IsInvariantMeasure P π) := by sorry

end SWSSNet.Diffusion
