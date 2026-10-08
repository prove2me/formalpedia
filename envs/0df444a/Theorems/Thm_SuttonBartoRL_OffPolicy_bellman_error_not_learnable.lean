-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_bellman_error_not_learnable
-- name    : SuttonBartoRL.OffPolicy.bellman_error_not_learnable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:03:16.567991+00:00
-- url     : https://prove2.me/theorems/e6181a1e-3b48-4113-bafa-06e0d7bf5ea7
-- title:
--   Example 11.4 — two MRPs with the same data distribution have different BE at w = 0
-- statement:
--   Take the two Markov reward processes of Example 11.4 with their features, and any discount $\gamma\in[0,1]$. At $\mathbf w = \mathbf 0$:
--
--   1. in the left MRP the Bellman error vector is zero, so $\mathrm{BE}(\mathbf 0) = 0$ for every state weighting $\mu$;
--   2. hence in the left MRP $\mathbf w=\mathbf 0$ minimizes the BE for every nonnegative $\mu$;
--   3. in the right MRP, with $\mu(s) = \tfrac13$,
--   $$
--   \mathrm{BE}(\mathbf 0) = \mu(\mathsf B)\cdot 1 + \mu(\mathsf B')\cdot 1 = \tfrac23 .
--   $$
--   4. $\mu(s) = \tfrac13$ is a stationary distribution of the right MRP, and $\mu_1 = (\tfrac13, \tfrac23)$ one of the left MRP;
--   5. the two MRPs, each started from its stationary distribution, generate the same observable data distribution: for every $n$, every initial observation $o_0$ and all rewards and observations $(r_1, o_1), \dots, (r_n, o_n)$, the probability of observing $\mathbf x(S_0) = o_0, R_1 = r_1, \mathbf x(S_1) = o_1, \dots, R_n = r_n, \mathbf x(S_n) = o_n$ is the same in both.
--
--   Since the two MRPs generate the same data distribution, the BE is not a function of the data: it is not learnable.
--
--   **Formalization Note** The MRPs are the ones of the definition item, transcribed from the figure on p. 276. The book does not give $\mu$ for the left MRP; claims 1–2 hold for every $\mu$. The data distribution is described by all finite prefixes of the observed stream (feature vectors and rewards), with each process started from its stationary distribution. The book's further remark on the BE minimizer of the right MRP as $\gamma\to1$ is not formalized.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 11.4, p. 276

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry
import Definitions.Def_SuttonBartoRL_OffPolicy_BELearnabilityExample

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), Example 11.4, p. 276. For every discount `γ ∈ [0, 1]`, at `w = 0`:
1. in the left MRP the Bellman error vector is zero, so `BE(0) = 0` for every state weighting `µ`;
2. hence in the left MRP `w = 0` minimizes the BE (for every nonnegative `µ`);
3. in the right MRP with `µ(s) = 1/3`, `BE(0) = µ(B)·1 + µ(B′)·1 = 2/3`;
4. `µ(s) = 1/3` is stationary for the right MRP, and `(1/3, 2/3)` for the left one;
5. the two MRPs, each started from its stationary distribution, generate the same observable data
   distribution: every finite sequence of observed feature vectors and rewards has the same
   probability in both. -/
theorem bellman_error_not_learnable (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (bellmanError beMRP1 (mrpPolicy (Fin 2)) γ beFeatures1 0 = 0 ∧
      ∀ μ : Fin 2 → ℝ, BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 0 = 0) ∧
    (∀ μ : Fin 2 → ℝ, (∀ s, 0 ≤ μ s) → ∀ w : Fin 2 → ℝ,
      BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 0
        ≤ BE beMRP1 (mrpPolicy (Fin 2)) γ μ beFeatures1 w) ∧
    BE beMRP2 (mrpPolicy (Fin 3)) γ beMu2 beFeatures2 0 = 2 / 3 ∧
    (∀ s' : Fin 3, ∑ s, beMu2 s * beMRP2.trans s () s' = beMu2 s') ∧
    (∀ s' : Fin 2, ∑ s, beMu1 s * beMRP1.trans s () s' = beMu1 s') ∧
    ∀ (o₀ : Fin 2 → ℝ) (l : List (ℝ × (Fin 2 → ℝ))),
      obsProb beMRP1 beMu1 beFeatures1 o₀ l = obsProb beMRP2 beMu2 beFeatures2 o₀ l := by sorry

end SuttonBartoRL.OffPolicy
