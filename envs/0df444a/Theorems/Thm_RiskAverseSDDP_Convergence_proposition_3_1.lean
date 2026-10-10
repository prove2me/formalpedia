-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
-- name    : RiskAverseSDDP.Convergence.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:25.870452+00:00
-- url     : https://prove2.me/theorems/4fbf7ff4-237b-479b-8a2b-d63e8476bbeb
-- title:
--   Proposition 3.1 — $\mathcal Q_t$ is convex, finite and continuous on $[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^{\hat\varepsilon}$
-- statement:
--   Consider the risk-averse multistage stochastic convex program (3.9) with its recourse functions $\mathcal Q_t$ defined by the dynamic programming equations (3.10)–(3.11) and (3.13), under the standing assumptions on $\Phi_{t,j}$ and $\mathcal P_t$ and Assumption (H2) with constant $\varepsilon>0$. Then for $t=2,\dots,T+1$ and every $0<\hat\varepsilon<\varepsilon$, the recourse function $\mathcal Q_t$ is convex, finite on
--   $$
--   [\mathcal X_1\times\dots\times\mathcal X_{t-1}]^{\hat\varepsilon},
--   $$
--   and continuous on $[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^{\hat\varepsilon}$.
--
--   Here $[\cdot]^{\hat\varepsilon}$ is the $\hat\varepsilon$-fattening in $\mathbb R^{n(t-1)}$ with the Euclidean norm. This regularity of the recourse functions is what makes the cuts of Algorithm 1 well defined and uniformly Lipschitz.
--
--   **Formalization Note** $\mathcal Q_t$ is `Q (t-1)` in Lean (its argument is the history $x_{1:t-1}$). "Convex" is convexity of the extended-real function on all of $\mathbb R^{n(t-1)}$ (convex epigraph); continuity is continuity of its real values on the fattening, where they are finite by the second claim. The fattening is the closed thickening.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 7, Proposition 3.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model

namespace RiskAverseSDDP.Convergence

theorem proposition_3_1 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) :
    ∀ h, 1 ≤ h → h ≤ T → ∀ ε', 0 < ε' → ε' < ε →
      EConvex (D.Q h) ∧
      (∀ x ∈ Metric.cthickening ε' (D.prodSet h), D.Q h x ≠ ⊥ ∧ D.Q h x ≠ ⊤) ∧
      ContinuousOn (fun x => (D.Q h x).toReal) (Metric.cthickening ε' (D.prodSet h)) := by sorry

end RiskAverseSDDP.Convergence
