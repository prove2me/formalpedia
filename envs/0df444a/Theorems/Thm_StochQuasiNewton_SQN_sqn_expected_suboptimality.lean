-- Prove2me | Theorems.Thm_StochQuasiNewton_SQN_sqn_expected_suboptimality
-- name    : StochQuasiNewton.SQN.sqn_expected_suboptimality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:41:55.612985+00:00
-- url     : https://prove2.me/theorems/ad7ec436-d1ba-4f40-965b-4dd581a30c41
-- title:
--   Corollary 3.3 — expected suboptimality Q(β)/k for the SQN method (corrected constant)
-- statement:
--   Let $f_1,\dots,f_N$ be $C^2$ functions on $\mathbb R^n$, $F=\frac1N\sum_if_i$, and let $w^*$ minimize $F$. Let $M,L\ge1$, $1\le b\le N$, $1\le b_H\le N$, $0<\lambda$, $0<\Lambda$, and assume $\lambda I\prec\nabla^2F_{\mathcal S_H}(w)\prec\Lambda I$ for all $w$ and all samples of size $b_H$ (3.3). Then there are constants $0<\mu_1\le\mu_2$, depending only on these data, such that:
--
--   1. along every run of Algorithm 1 with gradient samples of size $b$ and Hessian samples of size $b_H$ whose correction vectors $s_t$ ($t\ge1$) are nonzero, the matrix applied at every iteration $k\ge1$ (the identity for $k\le2L$, otherwise $H_t$) lies strictly between $\mu_1I$ and $\mu_2I$;
--   2. for every $\beta>1/(2\mu_1\lambda)$, every $\gamma$ and every $w^1$: if, on every sample history, the correction vectors are nonzero and $\frac1N\sum_{i=1}^N\|\nabla f_i(w^k)\|^2\le\gamma^2$ at every iterate, then Algorithm 1 with $\alpha^k=\beta/k$ satisfies, for every $k\ge1$,
--   $$E[F(w^k)-F(w^*)]\le\frac{Q_c(\beta)}k,\qquad Q_c(\beta)=\max\Big\{\frac{\Lambda\mu_2^2\beta^2\gamma^2}{2(2\mu_1\lambda\beta-1)},\ \Lambda\mu_2^2\beta^2\gamma^2,\ F(w^1)-F(w^*)\Big\},$$
--   where the expectation is over independent samples $\mathcal S_k$, uniform among the $b$-element subsets, and $\mathcal S_{H,t}$, uniform among the $b_H$-element subsets.
--
--   This is the paper's main convergence result: the SQN method attains the same $O(1/k)$ expected suboptimality rate as stochastic gradient descent.
--
--   **Formalization Note** *Corrected constant:* the paper's $Q(\beta)$ (3.24) lacks the middle entry and the bound is false with it (see Theorem 3.2). *Assumption 1(3)* is imposed at the iterates, with $\xi$ uniform over the training set as in (1.1)–(1.3). *$\mu_2$* is undefined in the paper's corollary; it is Lemma 3.1's constant, and both constants also cover the stochastic gradient steps ($H=I$) that Algorithm 1 takes for $k\le2L$; the paper's "$\|H_k^{-1}\|\le1/\mu_1$" is implied by clause 1. *$s_t\neq0$* is assumed because Algorithm 2 is undefined otherwise. The proof in the paper refers to "step 10 of Algorithm 1"; the iteration is step 8.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1018, Corollary 3.3, Eqs. (3.23)–(3.24)

import Mathlib
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS
import Definitions.Def_StochQuasiNewton_SQN_Algorithm
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike

open scoped RealInnerProductSpace

namespace StochQuasiNewton.SQN

/-- Corollary 3.3 (corrected constant): for the finite-sum problem (1.3) with `C²` losses whose
subsampled Hessians of size `b_H` satisfy `λ I ≺ ∇²F_{S_H}(w) ≺ Λ I` (3.3), and a minimizer `w*`
of `F`, there are constants `0 < μ₁ ≤ μ₂`, depending only on the problem data, such that
(a) along every run of Algorithm 1 whose correction vectors `s_t` (`t ≥ 1`) are nonzero, every
matrix applied at an iteration `k ≥ 1` (the identity or `H_t`) satisfies `μ₁ I ≺ · ≺ μ₂ I`; and
(b) for every `β > 1/(2 μ₁ λ)`, every `γ` and every `w¹`: if on every sample history the
correction vectors are nonzero and `(1/N) ∑_i ‖∇f_i(w^k)‖² ≤ γ²` at every iterate, then with
`α^k = β/k`, `E[F(w^k) − F(w*)] ≤ Q_c(β)/k` for every `k ≥ 1`, the expectation being over
independent uniform samples `S_k` of size `b` and `S_{H,t}` of size `b_H`. -/
theorem sqn_expected_suboptimality {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (M L b bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH)
    (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn (objective f) Set.univ wstar) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      (∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
        (∀ t, 1 ≤ t → sqnPairS f M L α w1 S SH t ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k -
              μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              sqnAppliedMatrix f M L α w1 S SH k).PosDef) ∧
      (∀ (β γ : ℝ) (w1 : EuclideanSpace ℝ (Fin n)), 1 / (2 * μ₁ * lam) < β →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ t, 1 ≤ t → sqnPairS f M L (fun k => β / k) w1 S SH t ≠ 0) →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ k, 1 ≤ k →
            (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) (sqnIterate f M L (fun k => β / k) w1 S SH k)‖ ^ 2
              ≤ γ ^ 2) →
        ∀ k, 1 ≤ k →
          sampleExpectation N b bH k (fun S SH =>
              objective f (sqnIterate f M L (fun k => β / k) w1 S SH k) - objective f wstar) ≤
            rateConstant Lam lam μ₁ μ₂ β γ (objective f w1 - objective f wstar) / k) := by sorry

end StochQuasiNewton.SQN
