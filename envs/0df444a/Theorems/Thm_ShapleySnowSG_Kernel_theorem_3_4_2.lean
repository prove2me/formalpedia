-- Prove2me | Theorems.Thm_ShapleySnowSG_Kernel_theorem_3_4_2
-- name    : ShapleySnowSG.Kernel.theorem_3_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:03.225997+00:00
-- url     : https://prove2.me/theorems/9151b721-6664-4bbc-8215-bd316dfc6cad
-- title:
--   Theorem 3.4.2, p. 17 — v^k_λ is the unique zero of val(Δ̇ᵏ − wΔ̇⁰), drops its rank, is a root of some Pᵏ ∈ Eᵏ, and is algebraic of degree ≤ rank Δ̇⁰
-- statement:
--   Consider a two-player zero-sum stochastic game with $n\ge1$ states, finite nonempty action sets $I_k,J_k$, payoff $g$, transition probabilities $q(\cdot\mid k,i,j)$ and discount factor $\lambda\in(0,1]$, and let $v_\lambda\in\mathbb R^n$ be its vector of discounted values. For every state choose a Shapley–Snow kernel $\dot I_k\times\dot J_k$ of the local game $\mathcal G^k(\lambda,v_\lambda)$; let $\Delta^0,\dots,\Delta^n$ be the auxiliary matrices of the data array $D(\lambda)$ and $\dot\Delta^0,\dots,\dot\Delta^n$ those of the reduced array $\dot D(\lambda)$. Let $E^k$ be the set of polynomials $w\mapsto\det$ of a square sub-matrix of $\Delta^k-w\Delta^0$ that are nonzero and of degree at most $\mathrm{rank}(\dot\Delta^0)$. Fix a state $k$. Then:
--
--   1. $v^k_\lambda$ is the unique $w\in\mathbb R$ satisfying $\mathrm{val}(\dot\Delta^k-w\dot\Delta^0)=0$;
--   2. $\mathrm{rank}(\dot\Delta^k-v^k_\lambda\dot\Delta^0)<\max_{w\in\mathbb R}\mathrm{rank}(\dot\Delta^k-w\dot\Delta^0)$;
--   3. there exists $P^k\in E^k$ such that $P^k(v^k_\lambda)=0$;
--   4. if all the entries of $D(\lambda)$ are rational, $v^k_\lambda$ is algebraic of order at most $\mathrm{rank}(\dot\Delta^0)$:
--   $$[\mathbb Q(v^k_\lambda):\mathbb Q]\le\mathrm{rank}(\dot\Delta^0).$$
--
--   The theorem turns the computation of a discounted value into a univariate root-finding problem whose degree is controlled by the kernels, and bounds the algebraic degree of the value.
--
--   **Formalization Note** The conclusion holds for every choice of kernels (the paper fixes one arbitrary choice). $v_\lambda$ is any vector satisfying the Shapley fixed-point relation (unique by `shapley_fixed_point`). State $k\in\{1,\dots,n\}$ is `k : Fin n`, so $\Delta^k$ is `Delta … k.succ` and $\Delta^0$ is `Delta … 0`. Part 1 is the printed form, without the factor $(-1)^n$ of Result 1 (i), p. 4. "Algebraic of order at most $r$" is `IsAlgebraic ℚ v ∧ (minpoly ℚ v).natDegree ≤ r`. Action sets may depend on the state (§4, p. 20).
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, p. 17, Theorem 3.4.2 (E^k defined on p. 17; Result 1, p. 4)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_StochasticGame

namespace ShapleySnowSG.Kernel

open Matrix

/-- Theorem 3.4.2, p. 17: fix `λ ∈ (0, 1]` and a state `k`. Then
(i) `v^k_λ` is the unique `w ∈ ℝ` with `val(Δ̇^k − w Δ̇^0) = 0`;
(ii) `rank(Δ̇^k − v^k_λ Δ̇^0) < max_{w ∈ ℝ} rank(Δ̇^k − w Δ̇^0)`;
(iii) some `P^k ∈ E^k` has `P^k(v^k_λ) = 0`;
(iv) if all the entries of `D(λ)` are rational, `v^k_λ` is algebraic of order at most
`rank(Δ̇^0)`. -/
theorem theorem_3_4_2 {n : ℕ} (hn : 0 < n) {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    [∀ k, Nonempty (I k)] [∀ k, Nonempty (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ)
    (hq0 : ∀ k i j l, 0 ≤ q k i j l) (hq1 : ∀ k i j, ∑ l, q k i j l = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (v : Fin n → ℝ) (hv : IsShapleyFixed g q lam v)
    (s : Fin n → ℕ) (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k)
    (hK : ∀ k, IsSSK (localGame g q lam v k) (s k) (r k) (c k)) (k : Fin n) :
    (IsMatVal (DeltaDot g q lam s r c k.succ - v k • DeltaDot g q lam s r c 0) 0 ∧
      ∀ w : ℝ, IsMatVal (DeltaDot g q lam s r c k.succ - w • DeltaDot g q lam s r c 0) 0 →
        w = v k) ∧
    RankDrop (DeltaDot g q lam s r c k.succ) (DeltaDot g q lam s r c 0) (v k) ∧
    (∃ P ∈ Efam (Delta g q lam k.succ) (Delta g q lam 0) (DeltaDot g q lam s r c 0).rank,
      P.eval (v k) = 0) ∧
    ((∀ k' l i j, ∃ t : ℚ, dataArray g q lam k' l i j = (t : ℝ)) →
      IsAlgebraic ℚ (v k) ∧ (minpoly ℚ (v k)).natDegree ≤ (DeltaDot g q lam s r c 0).rank) := by sorry

end ShapleySnowSG.Kernel
