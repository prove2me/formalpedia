-- Prove2me | Theorems.Thm_Pegasos_Analysis_theorem_1
-- name    : Pegasos.Analysis.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:02.723971+00:00
-- url     : https://prove2.me/theorems/3583be8e-d727-4cc3-a631-f2a44ef2db60
-- title:
--   Theorem 1 — mini-batch Pegasos has average instantaneous objective within c(1 + ln T)/(2λT) of the optimum's
-- statement:
--   Let $\lambda > 0$ and let $S = (x_i,y_i)_{i\in[m]}$ be a training set with $x_i\in\mathbb R^n$, $y_i\in\{+1,-1\}$ and $\|x_i\|\le R$ for every $i$. Let $f(w) = \frac\lambda2\|w\|^2 + \frac1m\sum_{i}\max\{0,1-y_i\langle w,x_i\rangle\}$ be the SVM objective (1), let $w^\star$ be a minimiser of $f$ (Eq. (9)), and for a mini-batch $A$ of $k\ge1$ indices let $f(w;A) = \frac\lambda2\|w\|^2 + \frac1k\sum_{i\in A}\max\{0,1-y_i\langle w,x_i\rangle\}$ (Eq. (7)).
--
--   Run mini-batch Pegasos (Fig. 2) on any sequence of mini-batches $A_1, A_2,\dots$: $w_1 = 0$ and $w_{t+1} = P(w_t - \frac{1}{\lambda t}\nabla_t)$ with $\nabla_t$ the sub-gradient (8) of $f(\cdot;A_t)$ at $w_t$ and $P$ either the projection step (6) or the identity. Let
--   $$c = \begin{cases}(\sqrt\lambda + R)^2 & \text{with the projection step},\\ 4R^2 & \text{without it}.\end{cases}$$
--   Then for every $T\ge3$,
--   $$\frac1T\sum_{t=1}^T f(w_t;A_t) \;\le\; \frac1T\sum_{t=1}^T f(w^\star;A_t) + \frac{c\,(1+\ln T)}{2\lambda T}.$$
--
--   This is the paper's main convergence guarantee: the average instantaneous objective of the iterates approaches that of the SVM optimum at rate $O(\ln T/(\lambda T))$, with no dependence on the number of examples $m$. Expectation and high-probability bounds for random mini-batches follow from it.
--
--   **Formalization Note.** The bound is pathwise: it is stated for every sequence of mini-batches, so no probability space appears (the paper's proof never uses that $A_t$ is random). Mini-batches are $k$-tuples `Fin k → Fin m`; injective tuples are the subsets of Fig. 2 and non-injective ones the i.i.d. multi-sets the paper also allows (p. 9). Iterations are 1-based: $w_1 = 0$ and step $t\ge1$ uses $\eta_t = 1/(\lambda t)$ and the batch $A_t$ only. The flag `project : Bool` selects the variant, and $c$ is chosen by it. $\ln$ is `Real.log` of $T$ cast to $\mathbb R$.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, Theorem 1 (with Eq. (1), (2), (6)-(9) and Fig. 2)

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Theorem 1** (p. 11): assume `‖xᵢ‖ ≤ R` for every example, let `w⋆` minimise the SVM
objective (1) (Eq. (9)), and let `c = (√λ + R)²` with the projection step and `c = 4R²`
without. Then for every mini-batch sequence `A_1, A_2, …` and `T ≥ 3`, the mini-batch
Pegasos run of Fig. 2 satisfies
`(1/T) Σ_{t=1}^T f(w_t; A_t) ≤ (1/T) Σ_{t=1}^T f(w⋆; A_t) + c(1 + ln T)/(2λT)`. -/
theorem theorem_1 {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (project : Bool)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : ∀ w, svmObj lam x y wstar ≤ svmObj lam x y w)
    (T : ℕ) (hT : 3 ≤ T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, instObj lam x y (A t) (run lam x y A project t)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, instObj lam x y (A t) wstar
        + (if project then (Real.sqrt lam + R) ^ 2 else 4 * R ^ 2) * (1 + Real.log T)
          / (2 * lam * T) := by sorry

end Pegasos.Analysis
