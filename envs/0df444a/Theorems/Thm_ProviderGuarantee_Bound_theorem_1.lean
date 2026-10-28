-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_theorem_1
-- name    : ProviderGuarantee.Bound.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:40.523986+00:00
-- url     : https://prove2.me/theorems/ca1840a6-b2c5-418d-adfe-abb4298f5a59
-- title:
--   Theorem 1, p. 16 — the value loss under Pareto-efficient provider guarantees is at most max{δ, (n−1)/(n+(1−δ)(n−1))}
-- statement:
--   Let $D$ be a finite set of jobs with real values $v : D \to \mathbb R$, $v(S) = \sum_{d \in S} v(d)$, let $n$ providers have heterogeneity profile $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$ with $0 < \gamma_{\min} \le \gamma_{\max}$, and let $\delta = (\gamma_{\max} - \gamma_{\min})/\gamma_{\max}$. Let $\mathcal F$ be a set of allocations satisfying Assumption 1 (indivisibility, symmetry, monotonicity, provider independence) and let $\mathcal F_G \subseteq \mathcal F$ be a non-empty set of allocations with guarantees satisfying Assumption 2 (Pareto efficiency). Then the value loss (1) satisfies
--
--   $$\mathbf L_\gamma(\mathcal F, \mathcal F_G) = \frac{\max_{A \in \mathcal F} \sum_{i=1}^n \gamma_i v(A_i) - \max_{B \in \mathcal F_G} \sum_{i=1}^n \gamma_i v(B_i)}{\max_{A \in \mathcal F} \sum_{i=1}^n \gamma_i v(A_i)} \le \max\left\{\delta, \frac{n-1}{n + (1-\delta)(n-1)}\right\}.$$
--
--   Equivalently, $\sup_{\mathcal F, \mathcal F_G, \gamma} \mathbf L_\gamma(\mathcal F, \mathcal F_G)$ over all $\gamma \in [\gamma_{\min}, \gamma_{\max}]^n$ and all $\mathcal F, \mathcal F_G$ satisfying Assumptions 1 and 2 is at most this bound (5).
--
--   The bound depends only on the number of providers and the degree of heterogeneity. With homogeneous providers ($\delta = 0$) the loss never exceeds $\frac{n-1}{2n-1} < \frac12$, so imposing any Pareto-efficient guarantee (income guarantees, max-min fairness, α-fairness, §2.3) costs at most half of the optimal value.
--
--   **Formalization Note** Allocations are functions `Fin n → Finset D`. Maxima over $\mathcal F$ and $\mathcal F_G$ are real suprema of finite non-empty sets. When the optimal value over $\mathcal F$ is $0$, the page's ratio is $0/0$ and Lean's quotient is $0$. The statement quantifies over $D$, $v$, $n$, $\gamma_{\min}$, $\gamma_{\max}$ as well as over $\gamma$, $\mathcal F$, $\mathcal F_G$.
--
--   Differences from the source:
--   - encoding: sup_{F, F_G, γ} L_γ(F, F_G) ≤ bound → L_γ(F, F_G) ≤ bound for every γ, F, F_G satisfying the assumptions; reason: a supremum is at most a number iff every value is
--   - encoding: L_γ(F, F_G) is the ratio (1), which is 0/0 when max_F Σγ_i v(A_i) = 0 → valueLoss uses Lean's division, so the loss is 0 in that case; reason: only the instances where the page's ratio is undefined are affected; no hypothesis 0 < max_F is added
--   - reading: a set of jobs D (never said to be finite; v(S) is a finite sum and maxima over F are taken) → D a finite type; reason: the page writes v(S) = Σ_{d∈S} v(d) and max over F, which presuppose finitely many jobs; the paper calls D a discrete set of jobs
--   - encoding: providers N = {1, …, n} → indices i : Fin n (0, …, n−1); reason: Lean convention; a relabelling, same instances
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 16, Theorem 1, (5)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem theorem_1 {D : Type*} [Fintype D] [DecidableEq D] (n : ℕ) (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (hFG : FG.Nonempty) :
    valueLoss γ v F FG ≤ lossBound n (heterogeneity γmin γmax) := by sorry

end ProviderGuarantee.Bound
