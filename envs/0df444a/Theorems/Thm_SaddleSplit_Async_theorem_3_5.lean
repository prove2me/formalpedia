-- Prove2me | Theorems.Thm_SaddleSplit_Async_theorem_3_5
-- name    : SaddleSplit.Async.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:25.45965+00:00
-- url     : https://prove2.me/theorems/5ce86740-84e6-4cb8-9127-0160ae183410
-- title:
--   Theorem 3.5, p. 14 — Algorithm 3.4 converges weakly to a primal solution, a dual solution and a Kuhn–Tucker point of Problem 1.1
-- statement:
--   Consider the setting of Problem 1.1 and of Algorithm 3.4 under Assumptions 3.1–3.3: step sizes $\gamma_{i,n}\in[\varepsilon,1/(\alpha^\ell_i+\chi+\sigma)]$, $\mu_{k,n}\in[\varepsilon,1/(\beta^\ell_k+\sigma)]$, $\nu_{k,n}\in[\varepsilon,1/(\delta^\ell_k+\sigma)]$, $\sigma_{k,n}\in[\varepsilon,1/\varepsilon]$, where $\alpha=\min\{\alpha^c_i,\beta^c_k,\delta^c_k\}$, $\sigma>1/(4\alpha)$ and $1/\varepsilon>\max\{\alpha^\ell_i+\chi+\sigma,\beta^\ell_k+\sigma,\delta^\ell_k+\sigma\}$ (3.1); relaxations $\lambda_n\in[\varepsilon,2-\varepsilon]$; nonempty activated blocks $I_n\subset I$, $K_n\subset K$ with $I_0=I$, $K_0=K$ and every block activated at least once in every $P+1$ consecutive iterations; and lags $n-T\le\pi_i(n)\le n$, $n-T\le\omega_k(n)\le n$. Suppose that the dual problem (1.2) has a solution. Then, for every $i\in I$ and $k\in K$:
--
--   1. $\sum_n\|x_{i,n+1}-x_{i,n}\|^2<+\infty$;
--   2. $\sum_n\|y_{k,n+1}-y_{k,n}\|^2<+\infty$, $\sum_n\|z_{k,n+1}-z_{k,n}\|^2<+\infty$ and $\sum_n\|v^*_{k,n+1}-v^*_{k,n}\|^2<+\infty$;
--   3. $x_{i,n}-a_{i,n}\to0$, $y_{k,n}-b_{k,n}\to0$, $z_{k,n}-d_{k,n}\to0$ and $v^*_{k,n}-e^*_{k,n}\to0$;
--   4. there exist a solution $\overline x$ of (1.1) and a solution $\overline v^*$ of (1.2) such that
--   $$x_{i,n}\rightharpoonup\overline x_i,\qquad a_{i,n}\rightharpoonup\overline x_i,\qquad v^*_{k,n}\rightharpoonup\overline v^*_k,$$
--   and $(\overline x,\overline v^*)$ is a Kuhn–Tucker point of Problem 1.1 in the sense of (2.13).
--
--   Algorithm 3.4 activates the operators of Problem 1.1 separately (resolvents of $A_i$, $B^m_k$, $D^m_k$, forward steps for the other operators, the $L_{ki}$ and their adjoints), only on a subset of blocks per iteration, and with bounded delays; this theorem establishes its weak convergence.
--
--   **Formalization Note** A run is a predicate on given sequences pinning every assignment of (3.3), including the lagged indices inside every step size, the carry-over of inactive blocks (stated at $n+1$), $e_{k,n}$ recomputed for every $k$, and $\Delta_n$ with $(4\alpha)^{-1}$ evaluated at the current iterates. The resolvents are given maps satisfying the resolvent identity for every positive step. Dual solvability is the hypothesis `(dualSet prob).Nonempty`; nonemptiness of $I$ and $K$ follows from Assumption 3.2. When $\Delta_n>0$ the denominator of $\theta_n$ is positive, so the division is never by zero. The summability of a nonnegative series is the paper's "$<+\infty$".
-- source:
--   Bùi & Combettes, Multivariate monotone inclusions in saddle form, arXiv:2002.06135v3, p. 14, Theorem 3.5 (setting: Assumptions 3.1–3.3, p. 12; Algorithm 3.4, p. 13; proof pp. 14–19)

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

namespace SaddleSplit.Async
open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

/-- Theorem 3.5, p. 14: under Assumptions 3.1–3.3, if the dual problem (1.2) has a solution, every
run of Algorithm 3.4 has square-summable increments, `x_n − a_n → 0`, `y_n − b_n → 0`,
`z_n − d_n → 0`, `v*_n − e*_n → 0`, and `x_n ⇀ x̄`, `a_n ⇀ x̄`, `v*_n ⇀ v̄*` for a Kuhn–Tucker point
`(x̄, v̄*)` with `x̄ ∈ 𝒫` and `v̄* ∈ 𝒟`. -/
theorem theorem_3_5 {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp)
    (α σ ε : ℝ) (prm : Alg34Params I K) (h31 : Assumption31 prob α σ ε prm)
    (Pw : ℕ) (h32 : Assumption32 Pw prm) (T : ℕ) (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k)
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    (st : Alg34State H G) (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty) :
    (∀ i, Summable fun n => ‖st.x (n + 1) i - st.x n i‖ ^ 2) ∧
    (∀ k, Summable (fun n => ‖st.y (n + 1) k - st.y n k‖ ^ 2) ∧
      Summable (fun n => ‖st.z (n + 1) k - st.z n k‖ ^ 2) ∧
      Summable (fun n => ‖st.v (n + 1) k - st.v n k‖ ^ 2)) ∧
    (∀ i, Tendsto (fun n => st.x n i - st.a n i) atTop (𝓝 0)) ∧
    (∀ k, Tendsto (fun n => st.y n k - st.b n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.z n k - st.d n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.v n k - st.estar n k) atTop (𝓝 0)) ∧
    ∃ xbar ∈ primalSet prob, ∃ vbar ∈ dualSet prob, (xbar, vbar) ∈ ktSet prob ∧
      (∀ i, WeakTendsto (fun n => st.x n i) (xbar i) ∧ WeakTendsto (fun n => st.a n i) (xbar i)) ∧
      ∀ k, WeakTendsto (fun n => st.v n k) (vbar k) := by sorry

end SaddleSplit.Async
