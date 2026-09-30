-- Prove2me | Theorems.Thm_UnderstandingML_kdiam_two_approx
-- name    : UnderstandingML.kdiam_two_approx
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:18:01.59572+00:00
-- url     : https://prove2.me/theorems/42f34610-fc02-453a-9614-485b5f249312
-- title:
--   Exercise 3: farthest-first traversal with nearest-center clusters is a 2-approximation for the k-diam objective max_j diam(C_j)
-- statement:
--   **Exercise 3.** Given a metric space $(X, d)$ with $|X| < \infty$ and $k \in \mathbb{N}$, consider $G_{k\text{-diam}}((X, d), (C_1, \dots, C_k)) = \max_j \operatorname{diam}(C_j)$. The algorithm picks $\mu_1 = x$, then $\mu_j = \operatorname{argmax}_{x \in X}\min_{i \in [j-1]} d(x, \mu_i)$ for $j = 2, \dots, k$, and sets $C_i = \{x : i = \operatorname{argmin}_j d(x, \mu_j)\}$. It is a 2-approximation algorithm: $G_{k\text{-diam}}((X, d), (\hat C_1, \dots, \hat C_k)) \le 2\, G_{k\text{-diam}}((X, d), (C^*_1, \dots, C^*_k))$ for the optimal $C^*$.
--
--   Formally: for every partition $C^\star$ of $X$ into $k$ clusters and every $j$, some cluster $C^\star_{j'}$ has $\operatorname{diam}(\hat C_j) \le 2\operatorname{diam}(C^\star_{j'})$; ties in the argmax and argmin are arbitrary.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.8 p. 321, Exercise 3 with its hint (Gonzalez 1985)

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML

/-- **Exercise 3** (p. 321). Given a finite metric space `(X, d)` and `k`, the farthest-first
algorithm (`μ₁ = x`, `μⱼ = argmax_x min_{i<j} d(x, μᵢ)`, clusters by nearest center) is a
2-approximation for the k-diam objective `maxⱼ diam(Cⱼ)`: for every partition `C⋆` into `k`
clusters, `G_{k−diam}(Ĉ) ≤ 2 G_{k−diam}(C⋆)`, stated as: every cluster of `Ĉ` has diameter at
most twice the diameter of some cluster of `C⋆`. -/
theorem kdiam_two_approx {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ} (μ : Fin k → X)
    (hμ : IsFarthestFirst μ) (Chat : Fin k → Finset X) (hpart : IsPartition Finset.univ Chat)
    (hnear : IsNearestAssignment μ Chat) (Cstar : Fin k → Finset X)
    (hstar : IsPartition Finset.univ Cstar) (j : Fin k) :
    ∃ j' : Fin k, Metric.diam (↑(Chat j) : Set X) ≤ 2 * Metric.diam (↑(Cstar j') : Set X) := by sorry

end UnderstandingML
