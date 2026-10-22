-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_proposition_2
-- name    : RetailInfoShare.AFS.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:06.7033+00:00
-- url     : https://prove2.me/theorems/3f4bff0d-2d92-4f43-8ffe-307f0d2e9ba9
-- title:
--   Proposition 2, p. 17 — the optimal AFS strategy shares all signals truthfully with K∗ ∈ {⌊min{2/b−1,N}⌋, ⌈min{2/b−1,N}⌉} sellers, profit (8)
-- statement:
--   Assume the standing assumptions: $N \ge 1$ sellers, $0 < b \le 1$, $\sigma, t > 0$, $0 < \alpha < 1$. Let $m = \min\{2/b - 1, N\}$. Among all Asymmetric Full Sharing strategies (noise matrices with $m_{i_1 j} = m_{i_2 j}$ for all $i_1, i_2, j$, with entries in $[0,+\infty]$), and over all Bayesian equilibria of the sellers' Cournot game:
--
--   1. there is $K^*_{AFS} \in \{\lfloor m\rfloor, \lceil m \rceil\}$ such that sharing the full information $\{x_1,\dots,x_N\}$ truthfully with sellers $1, \dots, K^*_{AFS}$ and nothing with the others,
--   $$y_i(M^*_{AFS}) = \begin{cases} \{x_1,\dots,x_N\}, & i \le K^*_{AFS},\\ \emptyset, & \text{otherwise,}\end{cases}$$
--   is an optimal AFS strategy;
--   2. every equilibrium under this strategy gives the platform
--   $$\Pi^*_{AFS} = \frac{\alpha N a^2}{[2+b(N-1)]^2} + \frac{\alpha K^*_{AFS}\sigma^2}{[2+b(K^*_{AFS}-1)]^2\left(\sigma + \frac tN\right)};$$
--   3. the platform and every seller do at least as well in every such equilibrium as in every no-sharing equilibrium;
--   4. conversely, whenever sharing truthfully with sellers $1,\dots,K$ ($K \le N$) is an optimal AFS strategy, $K \in \{\lfloor m\rfloor, \lceil m \rceil\}$.
--
--   The result shows that a platform that owns the demand signals limits *who* is informed rather than *how precisely*: as substitution grows, fewer sellers receive the information, down to a single seller when $b = 1$.
--
--   **Formalization Note.** Optimality ranges over every AFS matrix with entries in $[0,+\infty]$ and every equilibrium of each, so the statement contains Proposition 1 for AFS. Equation (7) is read as the existence claim 1 together with the converse 4. The paper's sellers $1,\dots,K$ are the indices $0,\dots,K-1$, its "without loss of generality" choice of the informed group (p. 17). Profits are ex-ante expectations; see the Model file for the conventions and the added hypothesis $0 < \alpha < 1$.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 17, Proposition 2, eqs. (7)–(8)

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem proposition_2 (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) :
    (∃ K : ℕ, (K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) ∧
        IsOptimalAFS Z (truthfulGroup P.N K) ∧
        (∀ Q, IsEquilibrium Z (truthfulGroup P.N K) Q →
          platformProfit Z Q = PiNS P + sharingGain P K) ∧
        (∀ Q Q₀, IsEquilibrium Z (truthfulGroup P.N K) Q →
          IsEquilibrium Z (noSharing P.N) Q₀ →
          platformProfit Z Q₀ ≤ platformProfit Z Q ∧
            ∀ i, sellerProfit Z Q₀ i ≤ sellerProfit Z Q i)) ∧
    (∀ K : ℕ, K ≤ P.N → IsOptimalAFS Z (truthfulGroup P.N K) →
      K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) := by sorry

end RetailInfoShare.AFS
