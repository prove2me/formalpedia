-- Prove2me | Theorems.Thm_QiNonsmoothEq_Damped_unit_step_near
-- name    : QiNonsmoothEq.Damped.unit_step_near
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:32.704935+00:00
-- url     : https://prove2.me/theorems/6ac37869-11e7-418b-a11b-595195d481f5
-- title:
--   (4.2)–(4.5), proof of Theorem 4.3, p. 237 — near a semismooth, strongly BD-regular zero the damped Newton method takes the unit step and halves the error
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^n$ be locally Lipschitz and B-differentiable at every point. Fix $\beta\in(0,1)$ and $\sigma\in(0,1/2)$, and let $\{x^k\}$, $\{d^k\}$, $\{\alpha_k\}$ be a run of the damped Newton method (Algorithm 4.1) with $s=1$, with $F(x^k)\ne0$ for all $k$. Let $x^*$ be a zero of $F$ at which $F$ is semismooth and strongly BD-regular, and assume $F$ is semismooth on a neighbourhood of $x^*$.
--
--   Then there is $\bar\delta>0$ such that for every $k$ with $\|x^k-x^*\|\le\bar\delta$,
--   $$\alpha_k=1,\qquad x^{k+1}=x^k+d^k,\qquad \|x^{k+1}-x^*\|\le\tfrac12\|x^k-x^*\|.$$
--
--   These are (4.3), (4.4) and the first inequality of (4.2) in the paper's proof of Theorem 4.3; the last one yields (4.5), $\|x^{k+1}-x^*\|\le\delta$ whenever $\|x^k-x^*\|\le\delta\le\bar\delta$, so a ball around $x^*$ of radius at most $\bar\delta$ is invariant under the iteration.
--
--   **Formalization Note** Semismoothness on a neighbourhood of $x^*$ is an added hypothesis, inherited from Corollary 3.4 (its proof uses (2.16) at points near $x^*$, which Lemma 2.6 proves only at semismooth points). Global B-differentiability is the standing setting of Algorithm 4.1 (Theorem 4.2's "F is B-differentiable"). The first nonnegative integer passing (4.1) is $m_k$, so $\alpha_k=1$ means $m_k=0$.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 237, proof of Theorem 4.3, (4.2)–(4.5)

import Mathlib
import Definitions.Def_QiNonsmoothEq_Damped_Setting

namespace QiNonsmoothEq.Damped

open Filter Topology NonsmoothNewton.Local NonsmoothNewton.Shared

theorem unit_step_near {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : LocallyLipschitz F) (hB : ∀ y, BDiffAt F y)
    (β σ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ)
    (hrun : IsDampedNewtonRun F 1 β σ x d α) (hne : ∀ k, F (x k) ≠ 0)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hzero : F xstar = 0) (hss : SemismoothAt F xstar) (hreg : StronglyBDRegularAt F xstar)
    (hssN : ∀ᶠ y in 𝓝 xstar, SemismoothAt F y) :
    ∃ δbar > 0, ∀ k, ‖x k - xstar‖ ≤ δbar →
      α k = 1 ∧ x (k + 1) = x k + d k ∧ ‖x (k + 1) - xstar‖ ≤ (1 / 2) * ‖x k - xstar‖ := by sorry

end QiNonsmoothEq.Damped
