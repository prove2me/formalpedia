-- Prove2me | Theorems.Thm_PESContracts_Linear_theorem_1
-- name    : PESContracts.Linear.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:41.203317+00:00
-- url     : https://prove2.me/theorems/be70bf33-dcdd-4e12-9a0c-3e6b6327fc25
-- title:
--   Theorem 1, p. 10 — price k/2 achieves at least half of the optimal contract payoff
-- statement:
--   Fix positive initial forest area $a_0$, cost curvature $h$, and environmental value $k$. Let $\mu$ be any probability distribution supported on $[\underline\theta,\bar\theta]\subseteq[0,1]$. Every agent best-response selection $a_L$ to the linear price $k/2$ gives a principal payoff at least half the payoff of every feasible, integrable direct revelation contract $(a,P)$:
--
--   $$
--   \mathbb E_\mu[k a(\theta)-P(\theta)]
--   \leq 2\mathbb E_\mu[(k-k/2)a_L(\theta)].
--   $$
--
--   Consequently the best linear contract, whose payoff is $\operatorname{Obj}^{L*}=\sup_{p\geq0}\operatorname{Obj}^L(p)$, also achieves at least half of every such contract's payoff. The theorem compares with actual contract payments, subject to individual rationality and incentive compatibility.
--
--   **Formalization Note** The bound over every feasible contract expresses the paper's comparison with the optimal payoff without requiring an attained maximum. The type law may have atoms; only the contract's action and payment require integrability. Positive $a_0$ makes the threshold $1-p/(ha_0)$ meaningful.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), p. 10, Theorem 1, with model in pp. 4–5 and proof in pp. 24–26; https://ssrn.com/abstract=3754041

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
open MeasureTheory

namespace PESContracts.Linear

/-- Theorem 1, p. 10: price k/2 earns at least half of every feasible contract payoff. -/
theorem theorem_1 (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ M.typesᶜ = 0) :
    (∀ aL : ℝ → ℝ, IsLinearBestResponse M (k / 2) aL →
      ∀ C : DirectContract, C.Feasible M →
        Integrable C.a μ → Integrable C.P μ →
        C.payoff k μ ≤ 2 * ∫ θ, (k - k / 2) * aL θ ∂μ) ∧
    (∀ C : DirectContract, C.Feasible M →
        Integrable C.a μ → Integrable C.P μ →
        C.payoff k μ ≤ 2 * ObjLstar M k μ) := by sorry

end PESContracts.Linear
