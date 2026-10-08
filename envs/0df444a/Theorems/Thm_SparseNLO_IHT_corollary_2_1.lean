-- Prove2me | Theorems.Thm_SparseNLO_IHT_corollary_2_1
-- name    : SparseNLO.IHT.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:24.286556+00:00
-- url     : https://prove2.me/theorems/3939510c-208c-4a69-8853-f2a8d351e875
-- title:
--   Corollary 2.1 — an L-stationary point (L > 0) is a basic feasible point
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below (Assumption 1), and let $0<s<n$. If $x^*$ is an $L$-stationary point of (P) for some $L>0$, i.e. $x^*\in C_s$ and $x^*\in P_{C_s}\big(x^*-\tfrac1L\nabla f(x^*)\big)$, then $x^*$ is a basic feasible (BF) point:
--   $$\|x^*\|_0<s\ \Rightarrow\ \nabla f(x^*)=0,\qquad \|x^*\|_0=s\ \Rightarrow\ \nabla_i f(x^*)=0\ \text{ for all } i\in I_1(x^*).$$
--
--   Together with Lemma 2.1 it confines the possible limits of the IHT method for least squares to a finite set.
--
--   **Formalization Note** Assumption 1 is the paper's standing assumption and is kept although the implication does not use it.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 8, Corollary 2.1

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

open Filter Topology

namespace SparseNLO.IHT

/-- Corollary 2.1 (p. 8). If `x` is an `L`-stationary point for some `L > 0`, then `x` is a BF
point. -/
theorem corollary_2_1 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) (hx : IsLStationary f s L x) :
    SparseNLO.CWOpt.IsBF f s x := by sorry

end SparseNLO.IHT
