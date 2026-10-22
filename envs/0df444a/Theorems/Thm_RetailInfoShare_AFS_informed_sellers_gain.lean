-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_informed_sellers_gain
-- name    : RetailInfoShare.AFS.informed_sellers_gain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:00.974879+00:00
-- url     : https://prove2.me/theorems/bfc0c674-487f-45b8-a25f-7eb16aff1b8b
-- title:
--   §4, p. 19 — under truthful K-group sharing informed sellers strictly gain, the others earn the no-sharing profit
-- statement:
--   Assume the standing assumptions and let $0 \le K \le N$. Let $q$ be an equilibrium when the platform shares all signals truthfully with sellers $1,\dots,K$ and nothing with the rest, and let $q^0$ be an equilibrium under no sharing. Then
--   1. every informed seller $j \le K$ strictly gains: $\pi_j(q^0) < \pi_j(q)$;
--   2. every other seller $j > K$ earns exactly his benchmark: $\pi_j(q) = \pi_j(q^0)$.
--
--   Together with the platform's gain this shows that the optimal AFS strategy weakly benefits everybody.
--
--   **Formalization Note.** The paper's sellers $1,\dots,K$ are the indices $0,\dots,K-1$ in Lean.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), §4, p. 19, 'Sellers who receive the information can strictly benefit from the information …'

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem informed_sellers_gain (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (K : ℕ) (hK : K ≤ P.N) (Q Q₀ : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z (truthfulGroup P.N K) Q) (hQ₀ : IsEquilibrium Z (noSharing P.N) Q₀) :
    (∀ j : Fin P.N, (j : ℕ) < K → sellerProfit Z Q₀ j < sellerProfit Z Q j) ∧
    (∀ j : Fin P.N, K ≤ (j : ℕ) → sellerProfit Z Q j = sellerProfit Z Q₀ j) := by sorry

end RetailInfoShare.AFS
