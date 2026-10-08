-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_prop2_2_ii_ergodic_bound
-- name    : ProxMethodVI.Rate.prop2_2_ii_ergodic_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:10.028242+00:00
-- url     : https://prove2.me/theorems/50c932da-ea73-4b3f-874c-2bb5b85f8814
-- title:
--   Proposition 2.2(ii) (2.13), p. 234 — ε(z^N) ≤ (Θ(z₀) + Σε_t)/Σγ_t for the relaxed CPM
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, let $F$ be monotone on $Z$, and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Consider a run of the relaxed conceptual prox-method: $z_0\in Z$, and for every $t\ge1$, $\gamma_t>0$, $w_t\in Z$, $z_t=P_{z_{t-1}}(\gamma_tF(w_t))$ and
--   $$\langle\gamma_tF(w_t),w_t-z_t\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),z_t-z_{t-1}\rangle-\omega(z_t)\le\epsilon_t.\tag{2.11}$$
--   Let $N\ge1$ and $z^N=\big(\sum_{t=1}^N\gamma_t\big)^{-1}\sum_{t=1}^N\gamma_tw_t$. Then
--   $$\epsilon(z^N)\equiv\max_{u\in Z}\langle F(u),z^N-u\rangle\le\frac{\Theta(z_0)+\sum_{t=1}^N\epsilon_t}{\sum_{t=1}^N\gamma_t},\qquad \Theta(z_0)=\max_{z\in Z}\big[\omega(z)-\omega(z_0)-\langle\omega'(z_0),z-z_0\rangle\big].$$
--
--   This is the convergence guarantee of the conceptual prox-method. Its quantity $\epsilon(z^N)$ is the standard accuracy measure of an approximate weak solution of the variational inequality, and the basic implementation of §3 is analysed by verifying (2.11) with $\epsilon_t=0$.
--
--   **Formalization Note.** The bound on $\epsilon(z^N)$ is stated as $\langle F(u),z^N-u\rangle\le\text{bound}$ for every $u\in Z$, which is equivalent to the maximum being at most the bound. Only monotonicity of $F$ is assumed; the Lipschitz half of (2.1) is not used by the proof. The hypothesis "the relaxed algorithm does not terminate in the course of $N$ steps" is replaced by runs that never terminate, since (2.8) is not modelled. $N\ge1$ makes $\sum\gamma_t>0$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), p. 234, Proposition 2.2(ii), (2.11), (2.13)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem prop2_2_ii_ergodic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (F : E → E →L[ℝ] ℝ) (hmono : IsMonotoneOnWRT Z F)
    (γ ε : ℕ → ℝ) (z w : ℕ → E) (hrun : IsRelaxedRun Z F ω ω' γ ε z w)
    (N : ℕ) (hN : 1 ≤ N) (u : E) (hu : u ∈ Z) :
    F u (ergodicAvg γ w N - u)
      ≤ (theta Z ω ω' (z 0) + ∑ t ∈ Finset.Icc 1 N, ε t) / ∑ t ∈ Finset.Icc 1 N, γ t := by sorry

end ProxMethodVI.Rate
