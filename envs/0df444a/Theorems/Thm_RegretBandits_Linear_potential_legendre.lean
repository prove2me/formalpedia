-- Prove2me | Theorems.Thm_RegretBandits_Linear_potential_legendre
-- name    : RegretBandits.Linear.potential_legendre
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:15:35.058821+00:00
-- url     : https://prove2.me/theorems/4dbe616d-d68c-4f50-9d77-004f7880aa76
-- title:
--   Lemma 5.3 — $F_\psi$ is Legendre and its dual Bregman divergence is bounded by $\psi'$
-- statement:
--   Let $\psi:(-\infty,a)\to(0,+\infty)$ be a $0$-potential and let $F_\psi(x)=\sum_{i=1}^d\int_0^{x_i}\psi^{-1}(s)\,ds$ on $\bar D=[0,+\infty)^d$, with $D=(0,+\infty)^d$. Then $F_\psi$ is a Legendre function on $\bar D$ with dual space $D^*=\nabla F_\psi(D)=(-\infty,a)^d$, and for all $u,v\in D^*$ with $u_i\le v_i$ for $i=1,\dots,d$,
--   $$D_{F_\psi^*}(u,v)\ \le\ \frac12\sum_{i=1}^d\psi'(v_i)\,(u_i-v_i)^2 .$$
--
--   Combined with the OSMD bound, this lemma turns the dual-divergence term into the explicit second-moment term of Theorem 5.7 whenever the loss estimates are non-negative.
--
--   **Formalization Note** The identity $D^*=(-\infty,a)^d$, which the book writes inside the statement, is stated as a separate conclusion. Membership $u_i<a$ is expressed in the extended reals, since $a$ may be $+\infty$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 79, Lemma 5.3 (with Definition 5.4)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_Potential

namespace RegretBandits.Linear

/-- Lemma 5.3 (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 79). Let `ψ` be a `0`-potential on
`(-∞, a)`. Then `F_ψ` is Legendre on the closure of `D = (0, +∞)^d`, its dual space is
`D* = ∇F_ψ(D) = (-∞, a)^d`, and for all `u, v ∈ D*` with `u_i ≤ v_i` for every `i`,
`D_{F*}(u, v) ≤ (1/2) ∑_{i=1}^d ψ'(v_i) (u_i - v_i)²`. -/
theorem potential_legendre {d : ℕ} {ψ : ℝ → ℝ} {a : EReal} (hψ : IsPotential 0 a ψ) :
    IsLegendre (potentialFn (d := d) ψ a 0) (posOrthant d) ∧
    grad (potentialFn ψ a 0) '' posOrthant d = {u : Fin d → ℝ | ∀ i, (u i : EReal) < a} ∧
    ∀ u v : Fin d → ℝ, (∀ i, (u i : EReal) < a) → (∀ i, (v i : EReal) < a) →
      (∀ i, u i ≤ v i) →
      dualBregman (potentialFn ψ a 0) (posOrthant d) u v ≤
        1 / 2 * ∑ i, deriv ψ (v i) * (u i - v i) ^ 2 := by sorry

end RegretBandits.Linear
