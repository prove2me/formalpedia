-- Prove2me | Theorems.Thm_SuperPolyak_proposition_4_1
-- name    : SuperPolyak.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:51.924979+00:00
-- url     : https://prove2.me/theorems/7276dc94-a035-434c-8aa6-0dc374439431
-- title:
--   Proposition 4.1 — $\operatorname{rank}(A_{i+1})=i+1$ and $\sigma_{i+1}(A_{i+1})\ge\min\{\|v_0\|,1\}(\alpha/(L\sqrt2))^i$
-- statement:
--   Let $v_0,v_1,\dots\in\mathbb R^d$ and let $A_j=[v_0^\top;\dots;v_{j-1}^\top]$ be the bundle matrices (with $A_0$ empty, so $\ker(A_0)=\mathbb R^d$). Fix $i\ge1$, $\alpha>0$ and $L$, and suppose that for all $j\le i$
--   $$
--   \|v_j\|\le L\qquad\text{and}\qquad \|P_{\ker(A_j)}v_j\|\ge\alpha .
--   $$
--   Then
--   $$
--   \operatorname{rank}(A_{i+1})=i+1\qquad\text{and}\qquad \sigma_{i+1}(A_{i+1})\ \ge\ \min\{\|v_0\|,1\}\Big(\frac{\alpha}{L\sqrt2}\Big)^{i}.
--   $$
--
--   This is the quantitative rank-growth estimate: as long as each new generalized gradient has a component of size at least $\alpha$ outside the span of the previous ones, the bundle matrix keeps full row rank and its pseudoinverse stays bounded. It is used in Item 1 of Lemma 4.7.
--
--   **Formalization Note** $\sigma_{i+1}$ is `singularValues i` (0-indexed).
--
--   Differences from the source:
--
--   - reading: min{‖A₀‖₂, 1} → min{‖v₀‖, 1}; reason: under Algorithm 2's convention A₀ is the empty matrix (‖A₀‖₂ = 0 would make the bound vacuous); the proof of Lemma 4.7 uses ‖A₀‖₂ = ‖v₀‖ ("since A₀ = [v₀ᵀ]"), i.e. ‖A₁‖₂
--   - reading: A_j with rows indexed as printed in §4.2 → A_j = [v₀ᵀ; …; v_{j−1}ᵀ], A₀ empty, ker(A₀) = ℝᵈ; reason: Algorithm 2's convention (A₁ := v₀ᵀ, A_{i+1} := [A_i; v_iᵀ]); at j = 0 the hypothesis reads ‖v₀‖ ≥ α
--   - reading: the constant L (Theorem 2.2's bound on g(B_δ(x̄))) → ‖v_j‖ ≤ L for all j ≤ i; reason: the proof iterates Lemma A.2, whose hypothesis ‖v‖ ≤ L is inherited; in §4.2 it holds because v_j ∈ g(y_j) with y_j ∈ B_δ(x̄)
--   - encoding: σ_{i+1} → LinearMap.singularValues i; reason: Mathlib's singular values are 0-indexed
-- source:
--   Charisopoulos & Davis, A superlinearly convergent subgradient method for sharp semismooth problems, arXiv:2201.04611v1, Proposition 4.1, p.25 (proved in Appendix A.2, p.48)

import Mathlib
import Definitions.Def_SuperPolyak_bundleMatrix

namespace SuperPolyak

/-- **Proposition 4.1** (Charisopoulos & Davis, arXiv:2201.04611v1, Proposition 4.1, p.25). Let
`v₀, …, v_i ∈ ℝᵈ` with `‖v_j‖ ≤ L` and let `A_j = [v₀ᵀ; …; v_{j−1}ᵀ]`. Fix `i ≥ 1` and suppose
that `‖P_{ker(A_j)} v_j‖ ≥ α > 0` for all `j ≤ i`. Then
`rank(A_{i+1}) = i + 1` and `σ_{i+1}(A_{i+1}) ≥ min{‖v₀‖, 1} · (α/(L√2))^i`.

**Formalization Note** Algorithm 2's convention: `A_j` has rows `v₀, …, v_{j−1}`, `A₀` is empty,
so `ker(A₀) = ℝᵈ` and the hypothesis at `j = 0` reads `‖v₀‖ ≥ α`. The paper's `‖A₀‖₂` is read as
`‖v₀‖ = ‖A₁‖₂` (the proof of Lemma 4.7 writes `A₀ = [v₀ᵀ]`). `‖v_j‖ ≤ L` is the hypothesis of
Lemma A.2, whose iteration is the proof; in §4.2 it is the bound of `L` on `g(B_δ(x̄))`.
`σ_{i+1} = singularValues i` (0-indexed). -/
theorem proposition_4_1 {d : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin d)) {α L : ℝ} (i : ℕ)
    (hi : 1 ≤ i) (hα : 0 < α)
    (hP : ∀ j ≤ i, α ≤ ‖(LinearMap.ker (bundleLin v j)).starProjection (v j)‖)
    (hL : ∀ j ≤ i, ‖v j‖ ≤ L) :
    (bundleMatrix v (i + 1)).rank = i + 1 ∧
      min ‖v 0‖ 1 * (α / (L * Real.sqrt 2)) ^ i ≤ (bundleLin v (i + 1)).singularValues i := by sorry

end SuperPolyak
