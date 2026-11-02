-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_theorem_5_null
-- name    : SWSSNet.Diffusion.theorem_5_null
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T22:30:47.837031+00:00
-- url     : https://prove2.me/theorems/d7d3961a-e037-46bb-a810-0b918e412315
-- title:
--   Theorem 5 (second assertion) — if $\vartheta_p=0$, no invariant probability measure under any stationary Markov control
-- statement:
--   Consider the multiclass multi-pool tree network in the Halfin–Whitt regime under complete resource pooling, and its limiting controlled diffusion
--
--   $$
--   dX_t=b(X_t,U_t)\,dt+\Sigma\,dW_t ,\qquad \Sigma=\mathrm{diag}(\sqrt{2\lambda_1},\dots,\sqrt{2\lambda_I}),
--   $$
--
--   with drift (42) built from the vector $h$ of (12). Let $p$ be a positive probability vector and $\vartheta_p$ the SWSS parameter, the optimal value of (LP′).
--
--   If $\vartheta_p=0$, then under every stationary Markov control $v$ (a Borel map from $\mathbb R^I$ into the control set $\Delta_I\times\Delta_J$) the diffusion cannot be positive recurrent. That is, for every family $P_t(x,\cdot)$ that is the transition probability of the strong solutions under $v$, there is no invariant probability measure $\pi$ with $\pi P_t=\pi$ for all $t\ge0$.
--
--   This is the second assertion of Theorem 5 in the source. Together with transience for $\vartheta_p<0$, it shows that positivity of $\vartheta_p$ is necessary for stabilizing the limiting diffusion.
--
--   **Formalization Note** "Cannot be positive recurrent" is formalized as the absence of an invariant probability measure for any transition probability `P` of the strong solutions (`IsStrongTransition`), exactly as in the corresponding clause of the mission's goal `SWSSNet.Diffusion.theorem_1`.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 22, Theorem 5 (second assertion: ϑ_p = 0)

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
/-- Theorem 5, p. 22, second assertion: if `ϑ_p = 0`, then under every stationary Markov control
the limiting diffusion (41) has no invariant probability measure. -/
theorem theorem_5_null {I J : ℕ} (N : TreeNetwork I J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    swss N p = 0 → ∀ v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ), IsMarkovControl v →
      ∀ P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I),
        IsStrongTransition (markovDrift N (hvec N) v) (Sigma N) P →
        ¬ ∃ π, GPhNGIDiffusion.EMError.IsInvariantMeasure P π := by sorry

end SWSSNet.Diffusion
