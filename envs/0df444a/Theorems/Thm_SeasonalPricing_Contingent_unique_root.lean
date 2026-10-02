-- Prove2me | Theorems.Thm_SeasonalPricing_Contingent_unique_root
-- name    : SeasonalPricing.Contingent.unique_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:10:42.157402+00:00
-- url     : https://prove2.me/theorems/4bc7a278-af43-4114-974c-13964d995d67
-- title:
--   Proof of Theorem 1 — equation (2) has a unique solution $\psi \ge p_1$
-- statement:
--   Let $(\pi, a)$ be a belief about the remaining inventory $Q_T \in \{0,\dots,Q\}$ and the allocation event $\mathcal A$, let $p_1$ be the premium price and $p_2(\cdot)$ any discount menu, $\alpha \ge 0$ and $0 \le t < T$. Assume that $\alpha > 0$ or that allocation is not sure, $\sum_{q=0}^{Q}\pi(q)a(q) < 1$. Then there is exactly one real number $\psi$ with $\psi \ge p_1$ and
--
--   $$
--   \psi - p_1 = \mathrm E_{Q_T}\!\left[\max\{\psi e^{-\alpha(T-t)} - p_2(Q_T), 0\}\cdot \mathbf 1\{\mathcal A \mid Q_T\}\right] = \sum_{q=0}^{Q} \pi(q)\,a(q)\,\max\{\psi e^{-\alpha(T-t)} - p_2(q), 0\}.
--   $$
--
--   This is the conclusion of the paper's uniqueness argument: the threshold $\psi(t)$ of Theorem 1 is well defined at every arrival time $t \in [0, T)$.
--
--   **Formalization Note** The paper writes "a unique value of $\psi \in [p_1, \infty]$". The root is infinite only when $\alpha = 0$ and allocation is sure; that case is excluded by the added hypothesis "$\alpha > 0$ or $\sum \pi a < 1$" (in it, (2) has no finite root or a whole half-line of roots), so the statement asserts a unique finite root. The paper's $p_2(q) \le p_1$ is not needed here.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 358, Proof of Theorem 1 ("Consequently, there exists a unique value of ψ ∈ [p₁, ∞] for which (2) holds.")

import Mathlib
import Definitions.Def_SeasonalPricing_Contingent_IsInventoryBelief
import Definitions.Def_SeasonalPricing_Contingent_waitingSurplus

namespace SeasonalPricing.Contingent

/-- Proof of Theorem 1 (Aviv–Pazgal 2008, p. 358): there is a unique `ψ ≥ p₁` solving (2),
`ψ - p₁ = E_{Q_T}[max{ψ e^{-α(T-t)} - p₂(Q_T), 0} · 1{𝒜 | Q_T}]`. -/
theorem unique_root (Q : ℕ) (pmf alloc p2 : ℕ → ℝ) (p1 α T t : ℝ)
    (hbelief : IsInventoryBelief Q pmf alloc) (hα : 0 ≤ α) (ht0 : 0 ≤ t) (htT : t < T)
    (hslope : 0 < α ∨ ∑ q ∈ Finset.range (Q + 1), pmf q * alloc q < 1) :
    ∃! ψ : ℝ, p1 ≤ ψ ∧ ψ - p1 = waitingSurplus Q pmf alloc p2 α T t ψ := by sorry

end SeasonalPricing.Contingent
