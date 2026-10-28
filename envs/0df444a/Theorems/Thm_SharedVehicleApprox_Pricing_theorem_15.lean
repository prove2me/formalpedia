-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_theorem_15
-- name    : SharedVehicleApprox.Pricing.theorem_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:11.312981+00:00
-- url     : https://prove2.me/theorems/c48ad6cd-54a2-4b5b-9ce2-7af9dc35020b
-- title:
--   Theorem 15, p. 18 — elevated-flow-relaxation prices earn at least m/(m+n−1) of the optimal state-dependent objective (corrected: q̃'s support graph strongly connected)
-- statement:
--   Consider the shared vehicle system with $n$ nodes, $m$ units and arrival rates $\varphi_{ij}\ge0$, and per-ride rewards $I_{ij}$ whose reward curves $R_{ij}(q)=q\,I_{ij}(q)$ are concave on $[0,1]$. Let $\tilde q$ be an optimal solution of the elevated flow relaxation program (Algorithm 1),
--   $$\max_q\ \sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})\quad\text{s.t.}\quad\sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}\ \ \forall i,\qquad q_{ij}\in[0,1],$$
--   whose support graph $\{(a,b):a\ne b,\ \varphi_{ab}\tilde q_{ab}>0\}$ is strongly connected, and let $\tilde\pi$ be a stationary law of the $m$-unit system in which $\tilde q$ is quoted at every non-empty station. Then for every state-dependent quantile policy $q$ and every stationary law $\pi$ of it,
--   $$\mathrm{Obj}_m(\tilde q)\ \ge\ \frac{m}{m+n-1}\,\mathrm{Obj}_m(q),$$
--   where $\mathrm{Obj}_m$ is the steady-state objective (2) under the respective law. In the paper's notation, $\mathrm{Obj}_m(\tilde q)\ge\frac{m}{m+n-1}\mathrm{Opt}_m$ (10).
--
--   The guarantee covers throughput, social welfare and revenue with regular value distributions simultaneously, and shows that a single convex program yields state-independent prices within a factor $m/(m+n-1)$ of the best state-dependent policy, whose description is exponential in $n$.
--
--   **Formalization Note** The state-independent $\tilde q$ is run as the state-dependent policy $x\mapsto\tilde q_{ij}\mathbf 1\{x_i>0\}$; since $R_{ij}(0)=0$ this gives the paper's (6). The ratio is written as a product, so no division by $\mathrm{Opt}_m$ occurs.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis on q̃ (the paper treats π as unique, p. 7, and assumes irreducibility, p. 16 and App. A) → hypothesis SupportConnected φ q̃; reason: the printed statement is false without it: n = 2, m = 2, φ ≡ 1, I_11 = I_22 = 1, I_12 = I_21 = 0; balanced demand forces q_12 = q_21, so q̃ = (1, 0, 0, 1) is optimal with value 2; every law on S_{2,2} is stationary under q̃, and π̃ = δ_{(2,0)} gives Obj_2(q̃) = 1, while the state-dependent policy x ↦ q̃·1{x_i > 0} with π = δ_{(1,1)} earns 2, and 2/3 · 2 = 4/3 > 1
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → the bound is stated against every state-dependent policy q (IsPolicy) and every stationary law π of it; reason: a bound against every (policy, law) pair is exactly a bound against their supremum, with no sSup and no attainment needed; p. 7 measures upper bounds against the best-possible steady-state distribution
--   - encoding: Obj_m(q̃), with "the" stationary distribution of q̃ and the ratio m/(m+n−1)·Opt_m → any stationary law π̃ of toPolicy q̃, and (m/(m+n−1))·Obj_m(q, π) ≤ Obj_m(toPolicy q̃, π̃); reason: under the connectivity hypothesis the stationary law is unique, and quantifying over all laws avoids assuming it; toPolicy builds in q̃_ij(x) = 0 at empty stations
--   - encoding: π is the steady-state distribution of the policy, treated as unique (p. 7) → π is any probability vector on S_{n,m}, zero off S_{n,m}, satisfying the balance equation (1) at every state; reason: p. 7: "our upper bounds are all with respect to the best-possible steady-state distribution"; (1) is the paper's characterization of stationarity, and Mathlib has no continuous-time Markov chains
--   - generalization: per-ride rewards I_ij(p_ij) of prices, with value distributions F_ij and I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile q ∈ [0, 1], with R_ij(q) := q · I_ij(q); no F_ij; reason: every I_ij induced by value distributions is such a function, so the statement specializes to the paper's; the density and F_ij(0) < 1 assumptions of p. 6 only make the price–quantile map a bijection
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 18 (PDF 19), Theorem 15, Eq. (10)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Theorem 15, p. 18 (corrected: the support graph of `q̃` is strongly connected): for
concave reward curves, the state-independent quantiles `q̃` returned by Algorithm 1 earn, under
any stationary law of the `m`-unit system, at least `m/(m+n−1)` times the objective of every
state-dependent policy under every stationary law of it: `Obj_m(q̃) ≥ m/(m+n−1) · Opt_m`. -/
theorem theorem_15 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (qt : Fin n → Fin n → ℝ) (hopt : IsRelaxOptimal φ I qt) (hconn : SupportConnected φ qt)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy qt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * obj n m φ I q π ≤ obj n m φ I (toPolicy qt) πt := by sorry

end SharedVehicleApprox.Pricing
