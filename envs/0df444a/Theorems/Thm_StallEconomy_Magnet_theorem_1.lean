-- Prove2me | Theorems.Thm_StallEconomy_Magnet_theorem_1
-- name    : StallEconomy.Magnet.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:06.976672+00:00
-- url     : https://prove2.me/theorems/8a2587b2-dcf8-4864-abb3-482b1f8af06a
-- title:
--   Theorem 1, p. 17 — doubly stochastic rendezvous matrix and unique uniform stationary law
-- statement:
--   Let $k,h\ge0$ be integers with $2h\le k$, where $h=\phi k$ is the allowed customer walking radius in grid units. A customer is uniform on $G_k=\{0,\ldots,k\}^2$ and the magnet rule determines the next rendezvous from any stall location in $\mathcal I_0$. Then the resulting matrix $\mathbb P$ is doubly stochastic, and a probability distribution $\pi$ on $\mathcal I_0$ is stationary exactly when it is uniform:
--   $$
--   \sum_{z_d\in\mathcal I_0}\mathbb P(z_o,z_d)
--   =\sum_{z_o\in\mathcal I_0}\mathbb P(z_o,z_d)=1,
--   \qquad
--   \pi\mathbb P=\pi\ \Longleftrightarrow\
--   \pi(z)=\frac{1}{|\mathcal I_0|}\quad(z\in\mathcal I_0).
--   $$
--
--   Thus the uniform law exists as a stationary distribution and is the only one. The paper uses this law to analyze the stall's repositioning distance under within-radius customer walking.
--
--   **Formalization Note** Mathlib's doubly-stochastic predicate also requires nonnegative entries, automatic for cardinality-based probabilities. The statement includes the door-to-door case $h=0$ and the boundary $2h=k$. The paper's subsequent informal passage $k\to\infty$ is outside this finite-grid theorem.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 17, Theorem 1; proof pp. 46–49

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem theorem_1 (k h : ℕ) (hkh : 2 * h ≤ k) :
    P k h ∈ doublyStochastic ℝ (inner k h) ∧
      ∀ π : inner k h → ℝ,
        MarkovChain.IsStationary (P k h) π ↔
          π = MarkovChain.unif (inner k h) := by sorry

end StallEconomy.Magnet
