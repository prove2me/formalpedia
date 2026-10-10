-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_4
-- name    : RiskAverseSDDP.Convergence.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:41.095981+00:00
-- url     : https://prove2.me/theorems/c19dbe0d-e57c-47a8-b4e9-80524d2419bf
-- title:
--   Lemma 3.4 — the new cut is tight at its trial point: $\mathcal Q^k_t(x^k_{[n^k_{t-1}]})=\theta^k_t$
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9), under the standing assumptions and Assumption (H2). For $t=2,\dots,T$ and all $k\ge1$,
--   $$
--   \mathcal Q^k_t\big(x^k_{[n^k_{t-1}]}\big)=\theta^k_t,\tag{3.23}
--   $$
--   where $n^k_{t-1}$ is the node of stage $t-1$ on the scenario sampled at iteration $k$ and $x^k_{[n^k_{t-1}]}$ the decision history leading to it.
--
--   Because the cuts of a stage are shared by all its nodes (interstage independence), the cut computed at iteration $k$ dominates all earlier cuts at its own trial point; this identity is used in the proof of Theorem 4.1 and gives the Lipschitz constant of Lemma 3.5.
--
--   **Formalization Note** In Lean, $t=s+2$: `Qm k (s+1)` is $\mathcal Q^k_t$, `hist k s (sampNode ys k s)` is $x^k_{[n^k_{t-1}]}$, and `θ k s` is $\theta^k_t$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 11, Lemma 3.4, (3.23)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

namespace RiskAverseSDDP.Convergence

theorem lemma_3_4 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ s, s + 2 ≤ T → ∀ k, 1 ≤ k →
      r.Qm k (s + 1) (r.hist k s (sampNode ys k s)) = r.θ k s := by sorry

end RiskAverseSDDP.Convergence
