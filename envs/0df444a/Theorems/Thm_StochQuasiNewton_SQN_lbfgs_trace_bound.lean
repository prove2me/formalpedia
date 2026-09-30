-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_lbfgs_trace_bound
-- name    : StochQuasiNewton.SQN.lbfgs_trace_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:52:45.557985+00:00
-- url     : https://prove2.me/theorems/8c346fec-528e-48ad-b4d8-53dac48e8d62
-- title:
--   Eq. (3.11) — trace bound for the direct L-BFGS matrices
-- statement:
--   Let $f_1,\dots,f_N$ be $C^2$ with $\lambda I\prec\nabla^2F_{\mathcal S_H}(w)\prec\Lambda I$ for every $w$ and every sample of size $b_H\ge1$, where $0<\lambda,\Lambda$. Let $M,t\ge1$, $\tilde m=\min\{t,M\}$, and let the correction pairs in memory, $(s_j,y_j)$ for $t-\tilde m<j\le t$, satisfy $s_j\neq0$ and $y_j=\nabla^2F_{\mathcal S_H}(\bar w)s_j$ for some point $\bar w$ and some sample $\mathcal S_H$ of size $b_H$. Then the direct L-BFGS matrices (3.7) satisfy
--   $$\operatorname{Tr}\big(B_t^{(\tilde m)}\big)\le\operatorname{Tr}\big(B_t^{(0)}\big)+\tilde m\Lambda .$$
--
--   Since $B_t^{(0)}=\frac{y_t^Ty_t}{s_t^Ty_t}I$ has trace at most $n\Lambda$ by (3.10), this bounds the largest eigenvalue of $B_{t+1}=B_t^{(\tilde m)}$ uniformly in $t$ (the constant $M_3$ of (3.11)).
--
--   **Formalization Note** The paper's chain also contains the intermediate bound by $\operatorname{Tr}(B_t^{(0)})+\sum_i\|y_{j_i}\|^2/(y_{j_i}^Ts_{j_i})$ and the final "$\le M_3$"; the statement records the explicit middle bound.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1016, Eq. (3.11)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Eq. (3.11): let `t ≥ 1`, `M ≥ 1`, `m̃ = min t M`, and let every pair `(s_j, y_j)` in the
memory window `t − m̃ < j ≤ t` have `s_j ≠ 0` and `y_j = ∇²F_{S_H}(w̄) s_j` for some point `w̄` and
some Hessian sample `S_H` of size `b_H`, where the subsampled Hessians of size `b_H` satisfy
(3.3). Then the direct L-BFGS matrix `B_{t+1} = B_t^{(m̃)}` satisfies
`Tr(B_t^{(m̃)}) ≤ Tr(B_t^{(0)}) + m̃ Λ`. -/
theorem lbfgs_trace_bound {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (bH : ℕ)
    (hbH : 1 ≤ bH)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (M t : ℕ) (hM : 1 ≤ M) (ht : 1 ≤ t) (s y : ℕ → EuclideanSpace ℝ (Fin n))
    (hpairs : ∀ j, t - min t M < j → j ≤ t →
      s j ≠ 0 ∧ ∃ (SH : Finset (Fin N)) (wbar : EuclideanSpace ℝ (Fin n)),
        SH.card = bH ∧ y j = subsampledHessian f SH wbar (s j)) :
    Matrix.trace (lbfgsDirectStage M t s y (min t M)) ≤
      Matrix.trace (lbfgsDirectStage M t s y 0) + (min t M : ℝ) * Lam := by sorry

end StochQuasiNewton.SQN
