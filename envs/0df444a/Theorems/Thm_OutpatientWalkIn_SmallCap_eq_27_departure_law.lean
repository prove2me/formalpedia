-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_eq_27_departure_law
-- name    : OutpatientWalkIn.SmallCap.eq_27_departure_law
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:36.322597+00:00
-- url     : https://prove2.me/theorems/9d591813-8e8e-40cd-be71-7fa1a1b14b50
-- title:
--   (27) and §C.1, Online App. p. 7 — the closed-form q_j is a probability vector solving the departure-epoch balance equations of the M/D/1/K−1+p queue
-- statement:
--   Consider the M/D/1/K−1+p queue with $K \ge 1$, $0 < p \le 1$ and $\rho = \lambda/\mu_S > 0$. Let $\alpha_j = \rho^je^{-\rho}/j!$, let $\alpha'_j = \sum_{k\ge0}(1-p)^k\alpha_{j+k}$ as in (24), and let $q_0,\dots,q_K$ be the closed form of §C.1 ($p=1$) and (27) ($0<p<1$). Then the following hold.
--
--   1. $q_j \ge 0$ for $0 \le j \le K$, and $\sum_{j=0}^{K} q_j = 1$.
--   2. For $0 \le j \le K-2$,
--   $$q_j = \alpha_0 q_{j+1} + \sum_{i=1}^{j}\alpha_i q_{j+1-i} + \alpha_j q_0 .$$
--   3. The last balance equation, in which arrivals that find $K$ customers join with probability $p$, holds:
--   $$q_{K-1} = \alpha'_0 q_K + \sum_{i=1}^{K-1}\alpha'_i q_{K-i} + \alpha'_{K-1}q_0 .$$
--
--   These are the balance equations of the queue length right after departures (Online Appendix p. 6), together with normalization. They determine the stationary law of that chain. So the theorem says that the closed form (27) is that stationary law, which is what makes $\pi(\delta,\mu_S) = 1 - 1/(q_0+\rho)$ the blocking probability of the appointment queue.
--
--   **Formalization Note** The statement takes general $K \ge 1$, $0<p\le1$ and $\rho>0$. Every such triple arises as $K = \lceil\delta\mu_S\rceil$, $p = \delta\mu_S+1-K$ for some $\delta\mu_S > 0$. For $p = 1$, $\alpha'_j = \alpha_j$ (Lean's $0^0 = 1$), and the last equation is the classical M/D/1/K one.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix pp. 6–7: balance equations and (24) (p. 6), §C.1 (p = 1) and §C.2, (26)–(27) (p. 7)

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.SmallCap
open Finset
theorem eq_27_departure_law (K : ℕ) (hK : 1 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ j, j ≤ K → 0 ≤ qVec K p ρ j) ∧
    (∑ j ∈ range (K + 1), qVec K p ρ j = 1) ∧
    (∀ j, j + 2 ≤ K → qVec K p ρ j = alphaP ρ 0 * qVec K p ρ (j + 1) + ∑ i ∈ Ico 1 (j + 1), alphaP ρ i * qVec K p ρ (j + 1 - i) + alphaP ρ j * qVec K p ρ 0) ∧
    (qVec K p ρ (K - 1) = alphaPrime p ρ 0 * qVec K p ρ K + ∑ i ∈ Ico 1 K, alphaPrime p ρ i * qVec K p ρ (K - i) + alphaPrime p ρ (K - 1) * qVec K p ρ 0) := by sorry
end OutpatientWalkIn.SmallCap
