-- Prove2me | Theorems.Thm_SuperPolyak_lemma_A_2
-- name    : SuperPolyak.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:48.194997+00:00
-- url     : https://prove2.me/theorems/27db3c14-7b37-45c8-aa8a-64281b6986f7
-- title:
--   Lemma A.2 — $\sigma_{k+1}([A;v^\top])\ge\frac{\alpha}{\sqrt2}\min\{1,\sigma_k(A)/L\}$ when $\|P_{\ker A}v\|>\alpha$
-- statement:
--   Let $A\in\mathbb R^{m\times d}$ have rank $k\ge1$, and let $v\in\mathbb R^d$ satisfy
--   $$
--   \|v\|\le L,\qquad \|P_{\ker(A)}(v)\|>\alpha>0,
--   $$
--   where $P_{\ker(A)}$ is the orthogonal projection onto $\ker(A)$. Then the stacked matrix $\begin{bmatrix}A\\ v^\top\end{bmatrix}$ satisfies
--   $$
--   \sigma_{k+1}\!\begin{bmatrix}A\\ v^\top\end{bmatrix}\ \ge\ \frac{\alpha}{\sqrt2}\,\min\Big\{1,\ \frac{\sigma_k(A)}{L}\Big\},
--   $$
--   where $\sigma_j(M)$ denotes the $j$-th largest singular value of $M$.
--
--   Appending a row with a component of size more than $\alpha$ outside the row space raises the rank by one while keeping the new smallest nonzero singular value away from $0$. Iterated, this is Proposition 4.1.
--
--   **Formalization Note** Matrices act on Euclidean space through `Matrix.toEuclideanLin`; `LinearMap.singularValues` is 0-indexed, so $\sigma_j$ is `singularValues (j-1)`. $L>0$ follows from the hypotheses.
--
--   Differences from the source:
--
--   - reading: rank(A) = k for some k ≤ d → rank(A) = k with 1 ≤ k; reason: σ_k(A) is defined only for k ≥ 1; k ≤ d is automatic
--   - encoding: σ_j, the j-th largest singular value (1-indexed) → LinearMap.singularValues (j − 1) of Matrix.toEuclideanLin; reason: Mathlib's singular values are 0-indexed; same values
-- source:
--   Charisopoulos & Davis, A superlinearly convergent subgradient method for sharp semismooth problems, arXiv:2201.04611v1, Lemma A.2, display (35), pp.47–48

import Mathlib
import Definitions.Def_SuperPolyak_bundleMatrix

namespace SuperPolyak

/-- **Lemma A.2** (Charisopoulos & Davis, arXiv:2201.04611v1, Lemma A.2, display (35),
pp.47–48). Let `A ∈ ℝ^{m×d}` and `v ∈ ℝᵈ` with `‖v‖ ≤ L` and `‖P_{ker(A)}(v)‖ > α > 0`, and
suppose `rank(A) = k`. Then
`σ_{k+1}([A; vᵀ]) ≥ (α/√2) · min{1, σ_k(A)/L}`.

**Formalization Note** `σ_j(M)` is the `j`-th largest singular value of `M` as a map
`ℝᵈ → ℝ^{rows}`; Mathlib's `LinearMap.singularValues` is 0-indexed, so `σ_j = singularValues (j − 1)`.
The matrices act through `Matrix.toEuclideanLin`, and `P_{ker(A)}` is the orthogonal projection
onto `ker(A)`. `σ_k(A)` is defined only for `k ≥ 1`, so `1 ≤ k` is assumed; `k ≤ d` is automatic.
`L > 0` follows from the hypotheses. -/
theorem lemma_A_2 {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d))
    {L α : ℝ} (hv : ‖v‖ ≤ L) (hα : 0 < α)
    (hPv : α < ‖(LinearMap.ker (Matrix.toEuclideanLin A)).starProjection v‖)
    (hrank : A.rank = k) (hk : 1 ≤ k) :
    α / Real.sqrt 2 * min 1 ((Matrix.toEuclideanLin A).singularValues (k - 1) / L) ≤
      (Matrix.toEuclideanLin (stackRow A v)).singularValues k := by sorry

end SuperPolyak
