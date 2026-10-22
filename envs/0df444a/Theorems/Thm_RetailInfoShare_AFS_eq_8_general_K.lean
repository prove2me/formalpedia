-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_eq_8_general_K
-- name    : RetailInfoShare.AFS.eq_8_general_K
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:04.542327+00:00
-- url     : https://prove2.me/theorems/72728eee-1521-40be-93cc-c45d04b9cb64
-- title:
--   Equation (8), p. 17, at a general group size K — truthful sharing with K sellers yields αNa²/[2+b(N−1)]² + αKσ²/([2+b(K−1)]²(σ+t/N))
-- statement:
--   Assume the standing assumptions and let $0 \le K \le N$. Suppose the platform shares all $N$ signals truthfully with sellers $1, \dots, K$ and nothing with the others. Then an equilibrium exists, and every equilibrium gives the platform the expected profit
--   $$\Pi = \frac{\alpha N a^2}{[2 + b(N-1)]^2} + \frac{\alpha K \sigma^2}{[2 + b(K-1)]^2\left(\sigma + \frac tN\right)}.$$
--
--   The second term is the platform's gain over no sharing; comparing it across $K$ is the integer optimization that determines the optimal group size.
--
--   **Formalization Note.** The paper displays this formula at the optimal size $K^*_{AFS}$ only (eq. (8)); the discussion on p. 18 ("we can examine how the total profits of the platform change with respect to the number of sellers she decides to share information with") treats $K$ as a variable. The paper's sellers $1,\dots,K$ are the indices $0,\dots,K-1$ in Lean.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 17, Equation (8), at general K as in §4, p. 18

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem eq_8_general_K (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (K : ℕ) (hK : K ≤ P.N) :
    (∃ Q, IsEquilibrium Z (truthfulGroup P.N K) Q) ∧
    ∀ Q, IsEquilibrium Z (truthfulGroup P.N K) Q →
      platformProfit Z Q = PiNS P + sharingGain P K := by sorry

end RetailInfoShare.AFS
