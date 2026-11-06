-- Prove2me | Theorems.Thm_PrefixVR_lemma_2
-- name    : PrefixVR.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:36.221008+00:00
-- url     : https://prove2.me/theorems/053d061c-4ce4-4f0a-a3fc-fdad96075e91
-- title:
--   Lemma 2 — variance of a prefix difference
-- statement:
--   Suppose condition (2) holds with constant $\delta$. Fix $x,y\in\mathbb R^d$ and a nonempty subset $A\subseteq[n]$ of size $k$. Define
--   $$
--   d_i=\nabla f_i(x)-\nabla f_i(y),\qquad d_A=\frac1k\sum_{i\in A}d_i .
--   $$
--   If $j$ is uniform on $A$, then
--   $$
--   \mathbb E_j\Big\|\frac kn\,(d_j-d_A)\Big\|^2\le\frac kn\,\delta^2\|x-y\|^2\le\delta^2\|x-y\|^2 .\qquad(24)
--   $$
--   Both inequalities are asserted.
--
--   This is the variance bound for the prefix reconstruction: a single sampled difference from the already inserted components costs at most $\frac kn\delta^2\|x-y\|^2$, uniformly in the prefix.
--
--   **Formalization Note** $\mathbb E_j$ over $j\sim\mathrm{Unif}(A)$ is the average $\frac1k\sum_{j\in A}$; $A$ is a `Finset (Fin n)`.
--
--   Differences from the source:
--   - generalization: the component gradients ∇fᵢ of differentiable fᵢ, with ∇f their average in (2) → arbitrary maps g i : ℝᵈ → ℝᵈ satisfying (2) with ∇f replaced by the average (1/n)∑ g i; reason: the statement and its proof use only (2); taking g i = ∇fᵢ, whose average is ∇f, gives the source's statement
--   - encoding: j ∼ Unif(A) and 𝔼_j → the average (1/k)∑_{j∈A}; reason: this is the expectation under the uniform law on A
--   - encoding: [n] and A ⊆ [n] → Fin n and A : Finset (Fin n); reason: Lean convention
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), App. A, Lemma 2, Eq. (24), p.12 (PDF p.12)

import Mathlib
import Definitions.Def_PrefixVR_Variation

namespace PrefixVR

/-- **Lemma 2 (variance of a prefix difference).** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient
Finite-sum Optimization without Full Gradient Refreshes* (manuscript, sha256 ed33106a…), Lemma 2,
Eq. (24), p.12: suppose (2) holds; fix `x, y` and a nonempty `A ⊆ [n]` of size `k`; with
`dᵢ = ∇fᵢ(x) − ∇fᵢ(y)` and `d_A = (1/k) ∑_{i∈A} dᵢ`, if `j ∼ Unif(A)` then
`𝔼_j ‖(k/n)(d_j − d_A)‖² ≤ (k/n) δ² ‖x − y‖² ≤ δ² ‖x − y‖²`.

**Formalization Note.** Components are `Fin n`; `g i` stands for `∇fᵢ` and (2) is `Variation g δ`
(with `∇f` the average of the `g i`). `𝔼_j` over `j ∼ Unif(A)` is the average `(1/k) ∑_{j∈A}`. -/
theorem lemma_2 {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hvar : Variation g δ) (x y : EuclideanSpace ℝ (Fin d)) (A : Finset (Fin n))
    (hA : A.Nonempty) :
    (A.card : ℝ)⁻¹ * ∑ j ∈ A,
        ‖((A.card : ℝ) / n) • ((g j x - g j y) -
          (A.card : ℝ)⁻¹ • ∑ i ∈ A, (g i x - g i y))‖ ^ 2
      ≤ (A.card : ℝ) / n * δ ^ 2 * ‖x - y‖ ^ 2 ∧
    (A.card : ℝ) / n * δ ^ 2 * ‖x - y‖ ^ 2 ≤ δ ^ 2 * ‖x - y‖ ^ 2 := by sorry

end PrefixVR
