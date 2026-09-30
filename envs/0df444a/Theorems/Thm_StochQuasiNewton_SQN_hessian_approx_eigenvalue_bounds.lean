-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_hessian_approx_eigenvalue_bounds
-- name    : StochQuasiNewton.SQN.hessian_approx_eigenvalue_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:36:49.160614+00:00
-- url     : https://prove2.me/theorems/6b156be1-793e-4761-834a-37ea07df14cd
-- title:
--   Lemma 3.1 — uniform eigenvalue bounds for the SQN Hessian approximations H_t
-- statement:
--   Let $f_1,\dots,f_N$ be $C^2$ functions on $\mathbb R^n$, let $0<\lambda$, $0<\Lambda$, and suppose that $\lambda I\prec\nabla^2F_{\mathcal S_H}(w)\prec\Lambda I$ for all $w$ and all samples $\mathcal S_H$ of size $b_H$, where $1\le b_H\le N$ (Assumption 1). Fix positive integers $M$ and $L$. Then there are constants $0<\mu_1\le\mu_2$ such that, for every run of Algorithm 1 (any step lengths, initial point and samples, with Hessian samples of size $b_H$) and every $t\ge1$ for which the correction vectors $s_1,\dots,s_t$ are nonzero, the Hessian approximation $H_t$ of Algorithm 2 satisfies
--   $$\mu_1I\prec H_t\prec\mu_2I .$$
--
--   The constants are fixed before the run: they do not depend on the step lengths, the initial point, the samples or $t$.
--
--   **Formalization Note** The paper's Algorithm 2 is undefined when some $s_j=0$ (it divides by $y_j^Ts_j$); the hypothesis $s_j\neq0$ for $1\le j\le t$ is added. The paper's "for all $\mathcal S_H\subseteq\{1,\dots,N\}$" in (3.3) is read as all samples of the size $b_H\ge1$ that Algorithm 1 draws, which excludes the empty sample (for which (2.3) is $0/0$). $\prec$ is `Matrix.PosDef` of the difference.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1015, Lemma 3.1, Eq. (3.6)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS
import Definitions.Def_StochQuasiNewton_SQN_Algorithm

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Lemma 3.1: under Assumption 1 (the losses are `C²` and every subsampled Hessian with `b_H`
samples satisfies `λ I ≺ ∇²F_{S_H}(w) ≺ Λ I`), there are constants `0 < μ₁ ≤ μ₂`, fixed before
the run, such that along every run of Algorithm 1 whose correction vectors `s_1, …, s_t` are
nonzero, the Hessian approximation of Algorithm 2 satisfies `μ₁ I ≺ H_t ≺ μ₂ I` (3.6). -/
theorem hessian_approx_eigenvalue_bounds {n N : ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (M L bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w)) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      ∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ t, (SH t).card = bH) →
        ∀ t, 1 ≤ t → (∀ j, 1 ≤ j → j ≤ t → sqnPairS f M L α w1 S SH j ≠ 0) →
          (sqnHessianApprox f M L α w1 S SH t - μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) - sqnHessianApprox f M L α w1 S SH t).PosDef := by sorry

end StochQuasiNewton.SQN
