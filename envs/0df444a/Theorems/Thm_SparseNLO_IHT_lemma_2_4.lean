-- Prove2me | Theorems.Thm_SparseNLO_IHT_lemma_2_4
-- name    : SparseNLO.IHT.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:56.051073+00:00
-- url     : https://prove2.me/theorems/ed65a858-2dbc-4e2e-9f97-8e796aa32dee
-- title:
--   Lemma 2.4 — a projected-gradient step y ∈ P_{C_s}(x − ∇f(x)/L) with L > L(f) decreases f by at least (L − L(f))/2 ‖x − y‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below (Assumption 1), and suppose its gradient is Lipschitz with constant $L(f)$ (Assumption 2):
--   $$\|\nabla f(x)-\nabla f(y)\|\le L(f)\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n.$$
--   Let $0<s<n$ and $L>L(f)$. Then for any $x\in C_s$ and any $y\in\mathbb R^n$ with
--   $$y\in P_{C_s}\Big(x-\tfrac1L\nabla f(x)\Big)\tag{2.7}$$
--   we have
--   $$f(x)-f(y)\ge\frac{L-L(f)}{2}\,\|x-y\|^2.\tag{2.8}$$
--
--   This sufficient-decrease inequality is what makes the IHT method a descent method; it yields Lemma 3.1 directly.
--
--   **Formalization Note** $L(f)$ is any constant `Lf : ℝ≥0` with `LipschitzWith Lf (gradient f)`; the result is claimed for every such constant. Assumption 1 is the paper's standing assumption and is kept as a hypothesis although this inequality does not need it. $P_{C_s}$ is the set of all nearest points of $C_s$.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), pp. 8–9, Lemma 2.4, (2.7)–(2.8)

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

open Filter Topology

namespace SparseNLO.IHT

/-- Lemma 2.4 (pp. 8–9). Under Assumption 2 (`∇f` is `L(f)`-Lipschitz) and `L > L(f)`, for any
`x ∈ C_s` and `y ∈ P_{C_s}(x − (1/L) ∇f(x))` (2.7),
`f(x) − f(y) ≥ (L − L(f))/2 · ‖x − y‖²` (2.8). Assumption 1 (f bounded below) is the paper's
standing assumption and is kept. -/
theorem lemma_2_4 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLip : LipschitzWith Lf (gradient f)) (L : ℝ) (hL : (Lf : ℝ) < L)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ SparseNLO.CWOpt.Cs n s)
    (hy : y ∈ projCs n s (x - (1 / L) • gradient f x)) :
    f x - f y ≥ (L - Lf) / 2 * ‖x - y‖ ^ 2 := by sorry

end SparseNLO.IHT
