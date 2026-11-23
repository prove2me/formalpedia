-- Prove2me | Theorems.Thm_PINNConvergence_nn_C0_convergence_implies_Ck
-- name    : PINNConvergence.nn_C0_convergence_implies_Ck
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:04:42.687858+00:00
-- url     : https://prove2.me/theorems/1817c0db-678e-41d2-bc81-450aa21e2a3c
-- title:
--   Lemma 2.1: bounded-weight networks converging in $C^0$ converge in $C^k$
-- statement:
--   Let $U\subset\mathbb{R}^d$ be a bounded domain and let $\mathcal H^{NN}_{\vec n}$ be the class of scalar networks with a fixed architecture $\vec n=(n_0,\dots,n_L)$ and activation $\sigma\in C^{k'}(\mathbb{R})$, where $k<k'$. Suppose that for each $s\in\{0,\dots,k\}$ the derivative $\sigma^{(s)}$ is bounded and Lipschitz continuous. Let $u\in C^k(\overline U)$, and let $h_j\in\mathcal H^{NN}_{\vec n}$ be networks whose weights and biases are uniformly bounded in $j$, with $h_j\to u$ in $C^0(\overline U)$. Then
--
--   $$h_j\to u\quad\text{in } C^k(\overline U),$$
--
--   that is, $\sup_U|D^{\mathbf s}h_j-D^{\mathbf s}u|\to0$ for every multi-index with $|\mathbf s|\le k$.
--
--   For networks of fixed size with bounded parameters, uniform convergence therefore upgrades to convergence of all derivatives that the activation controls.
--
--   **Formalization Note** Derivatives of order $j$ are compared through the $j$-th Fréchet derivative within $U$ with its operator norm. This gives the same convergence as the sup over multi-indices.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 2.2, Lemma 2.1, p. 8; proof in Appendix A (Claim A.1), pp. 19-21

import Mathlib
import Definitions.Def_PINNConvergence_Basic

open MeasureTheory Filter Topology

namespace PINNConvergence

theorem nn_C0_convergence_implies_Ck {d : ℕ} (U : Set (Rd d)) (hU : IsBoundedDomain U)
    (σ : ℝ → ℝ) (k k' : ℕ) (hkk' : k < k') (hσ : ContDiff ℝ k' σ)
    (hσb : ∀ s ≤ k, (∃ M : ℝ, ∀ t, |iteratedDeriv s σ t| ≤ M) ∧
      ∃ K : NNReal, LipschitzWith K (iteratedDeriv s σ))
    (L : ℕ) (n : ℕ → ℕ) (hn : IsArch L n) (u : Rd d → ℝ) (hu : IsCkClosure k U u)
    (W : ℕ → ∀ l, Matrix (Fin (n l)) (Fin (inWidth d n l)) ℝ) (b : ℕ → ∀ l, Fin (n l) → ℝ)
    (hbdd : ∃ M : ℝ, ∀ j, ParamsBounded L (W j) (b j) M)
    (hconv : TendstoUniformlyOn (fun j => nnEval σ d L n (W j) (b j)) u atTop (closure U)) :
    TendstoCk k U (fun j => nnEval σ d L n (W j) (b j)) u := by sorry

end PINNConvergence
