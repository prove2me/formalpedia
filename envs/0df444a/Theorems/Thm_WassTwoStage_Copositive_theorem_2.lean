-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_theorem_2
-- name    : WassTwoStage.Copositive.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:00:38.178666+00:00
-- url     : https://prove2.me/theorems/70b7e089-29a9-4059-a9c7-5e27d6c9ae38
-- title:
--   Theorem 2 — the copositive program (10) bounds the worst-case expectation from above
-- statement:
--   Assume the setting of §3 ($\Xi \ne \emptyset$, sufficiently expensive recourse, $I\ge1$, $\hat\xi_i\in\Xi$, $\epsilon\ge0$). For every first-stage decision $x$, the worst-case expectation is bounded above by the optimal value of the copositive program (10):
--   $$\mathcal Z(x) \le \overline{\mathcal Z}(x).$$
--   Here $\overline{\mathcal Z}(x)$ is the infimum of $\epsilon^2\lambda + \frac1I\sum_i[s_i + \boldsymbol q^\top\psi_i - \lambda\|\hat\xi_i\|_2^2 + \sum_j \phi_{ij}\boldsymbol q_j^2]$ over $\lambda\ge0$, $s_i$, $\psi_i$, $\phi_i$ such that the $3\times3$ block matrix of (10), built from the extended data (11), is copositive for every $i$.
--
--   The bound makes (1) amenable to a finite-dimensional conservative approximation; Theorem 4 shows it is tight under complete recourse.
--
--   **Formalization Note** The paper says "for any fixed $x \in \mathcal X$"; the statement here holds for every $x \in \mathbb R^{N_1}$, which is the same claim for every possible $\mathcal X$. The paper's proof goes through the dual (6), stated for $\epsilon > 0$; at $\epsilon = 0$ the bound follows from Proposition 1 and Theorem 3, so $\epsilon \ge 0$ is kept. Values are in `EReal`; $\overline{\mathcal Z}(x) = +\infty$ is possible (Example 1).
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 8, Theorem 2, (10), (11); proof pp. 9–10

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

namespace WassTwoStage.Copositive

/-- Theorem 2 (copositive upper bound), Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 8 (proof
pp. 9–10): under the standing assumptions of §3, for every first-stage decision `x` the
worst-case expectation `𝒵(x)` of (2) is at most the optimal value `𝒵̄(x) = 𝒵̄_0(x)` of the
copositive program (10). -/
theorem theorem_2 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hI : 0 < I)
    (hXi : d.Xi.Nonempty) (hSER : d.SufficientlyExpensiveRecourse)
    (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) (x : Fin N₁ → ℝ) :
    d.worstCase x ≤ d.upperValue 0 x := by sorry

end WassTwoStage.Copositive
