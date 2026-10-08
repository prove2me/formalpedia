-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_theorem3_2_two_step_rate
-- name    : ProxMethodVI.Rate.theorem3_2_two_step_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:08.716029+00:00
-- url     : https://prove2.me/theorems/e6a18fab-fab3-4377-b9c3-b6e996845f8d
-- title:
--   Theorem 3.2, p. 239 — with γ = α/(√2L), (3.4) holds within two inner iterations and ε(z^N) ≤ √2Θ(z₀)L/(αN)
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$ and conjugate norm $\|\cdot\|_*$, and let $Z\subseteq E$ be nonempty, convex and compact. Let $F$ satisfy (2.1) on $Z$ with constant $L>0$:
--   $$\|F(z)-F(z')\|_*\le L\|z-z'\|,\qquad\langle F(z)-F(z'),z-z'\rangle\ge0\qquad\forall z,z'\in Z.$$
--   Let $\omega$ be continuously differentiable on $Z$ and strongly convex with modulus $\alpha>0$ in the sense of (2.2), and let $P_z$ be its prox-mapping. Run the basic implementation of the prox-method with the stepsize $\gamma=\alpha/(\sqrt2L)$ of (3.2), from any $z_0\in Z$: at step $t$, $w_{t,1}=P_{z_{t-1}}(\gamma F(z_{t-1}))$; if (3.4) holds for $(z_{t-1},w_{t,1})$ then $w_t=z_{t-1}$ and $z_t=w_{t,1}$, and otherwise $w_t=w_{t,1}$ and $z_t=P_{z_{t-1}}(\gamma F(w_{t,1}))$. Then:
--
--   1. relation (3.4) holds at every step, in no more than two inner iterations:
--   $$\langle\gamma F(w_t),w_t-z_t\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),z_t-z_{t-1}\rangle-\omega(z_t)\le0\qquad\forall t\ge1;$$
--   2. for every $N\ge1$, the average $z^N=\frac1N\sum_{t=1}^Nw_t$ satisfies
--   $$\epsilon(z^N)\equiv\max_{u\in Z}\langle F(u),z^N-u\rangle\le\frac{\sqrt2\,\Theta(z_0)L}{\alpha N},\qquad\Theta(z_0)=\max_{z\in Z}\big[\omega(z)-\omega(z_0)-\langle\omega'(z_0),z-z_0\rangle\big].\tag{3.9}$$
--
--   This is the $O(1/N)$ rate of the mirror-prox method for variational inequalities with Lipschitz continuous monotone operators. Each step costs at most two evaluations of $F$ and two prox problems. In the Euclidean setup $\omega=\frac12\|\cdot\|_2^2$ the method is Korpelevich's extragradient method.
--
--   **Formalization Note.** Dual vectors are continuous linear functionals, and $\|\cdot\|_*$ is the operator norm; this is equivalent to the paper's inner-product setting with a second norm. The run is a relation that quantifies over every admissible choice of prox points. The inner loop is cut at $s=2$, which is exactly what claim 1 licenses. The termination test (2.8) is not modelled, so runs never stop; this only adds runs. With constant $\gamma_t=\gamma$, $z^N$ is the plain average of $w_1,\dots,w_N$ (the points $w_t$, not $z_t$). The bound on $\epsilon(z^N)$ is stated for every $u\in Z$, which is equivalent to the bound on the maximum. $L>0$ and $N\ge1$ are needed for (3.2) and (3.9) to make sense. The saddle-point bound (3.10) and the cost count "$2N$ computations of $F$" are not formalized.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), p. 239, Theorem 3.2, (3.9); basic implementation p. 237, (3.2)–(3.4)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem theorem3_2_two_step_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (F : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L) (hLip : IsLipschitzOnWRT Z F L)
    (hmono : IsMonotoneOnWRT Z F)
    (z w : ℕ → E) (hrun : IsBasicRun Z F ω ω' (α / (Real.sqrt 2 * L)) z w) :
    (∀ t : ℕ, test34 (α / (Real.sqrt 2 * L)) F ω ω' (z t) (w (t + 1)) (z (t + 1))) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ u ∈ Z,
        F u (((N : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 N, w t) - u)
          ≤ Real.sqrt 2 * theta Z ω ω' (z 0) * L / (α * N) := by sorry

end ProxMethodVI.Rate
