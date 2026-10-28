-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_9
-- name    : SharedVehicleApprox.Pricing.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:54.456112+00:00
-- url     : https://prove2.me/theorems/9c98d75e-782c-491d-a6ea-186a20c9e006
-- title:
--   Lemma 9, p. 15 — the elevated objective of the relaxation optimum q̃ bounds the objective of every state-dependent policy: Ôbj(q̃) ≥ Opt_m
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates and $I_{ij}$ per-ride rewards whose reward curves $R_{ij}(q)=q\,I_{ij}(q)$ are concave on $[0,1]$. Let $\tilde q$ be an optimal solution of the elevated flow relaxation program (Algorithm 1):
--   $$\max_q\ \sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})\quad\text{s.t.}\quad \sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}\ \ \forall i,\qquad q_{ij}\in[0,1].$$
--   Then for every state-dependent quantile policy $q$ of the $m$-unit system and every stationary law $\pi$ of it,
--   $$\mathrm{Obj}_m(q)=\sum_{x\in S_{n,m}}\pi(x)\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij}(x))\ \le\ \widehat{\mathrm{Obj}}(\tilde q)=\sum_{i,j}\varphi_{ij}R_{ij}(\tilde q_{ij}),$$
--   that is, $\widehat{\mathrm{Obj}}(\tilde q)\ge\mathrm{Opt}_m$.
--
--   This is the first step of the approximation framework: the convex relaxation upper-bounds the optimal state-dependent policy.
--
--   Differences from the source:
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → the bound is stated against every state-dependent policy q (IsPolicy) and every stationary law π of it; reason: a bound against every (policy, law) pair is exactly a bound against their supremum, with no sSup and no attainment needed; p. 7 measures upper bounds against the best-possible steady-state distribution
--   - encoding: π is the steady-state distribution of the policy, treated as unique (p. 7) → π is any probability vector on S_{n,m}, zero off S_{n,m}, satisfying the balance equation (1) at every state; reason: p. 7: "our upper bounds are all with respect to the best-possible steady-state distribution"; (1) is the paper's characterization of stationarity, and Mathlib has no continuous-time Markov chains
--   - generalization: per-ride rewards I_ij(p_ij) of prices, with value distributions F_ij and I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile q ∈ [0, 1], with R_ij(q) := q · I_ij(q); no F_ij; reason: every I_ij induced by value distributions is such a function, so the statement specializes to the paper's; the density and F_ij(0) < 1 assumptions of p. 6 only make the price–quantile map a bijection
--   - encoding: the pricing policy q̃ returned by the elevated flow relaxation program → any q̃ with IsRelaxOptimal φ I q̃ (feasible and maximizing Ôbj over the feasible set); reason: Algorithm 1 returns an optimal solution; the statement holds for each one, and existence is neither claimed nor needed
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 15 (PDF 16), Lemma 9; proof pp. 15–16 (PDF 16–17)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 9, p. 15: for concave reward curves, the elevated objective of an optimal solution `q̃`
of the elevated flow relaxation program (Algorithm 1) bounds the objective of every
state-dependent policy `q` under every stationary law `π` of it: `Ôbj(q̃) ≥ Opt_m`. -/
theorem lemma_9 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (qt : Fin n → Fin n → ℝ) (hopt : IsRelaxOptimal φ I qt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    obj n m φ I q π ≤ elevObj φ I qt := by sorry

end SharedVehicleApprox.Pricing
