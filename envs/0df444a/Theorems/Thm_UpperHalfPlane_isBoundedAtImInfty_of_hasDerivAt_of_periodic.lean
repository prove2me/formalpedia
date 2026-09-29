-- Prove2me | Theorems.Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic
-- name    : UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/6ab34a64-cfbc-517b-b670-33bca77557e8
-- title:
--   Periodic primitives of bounded periodic holomorphic functions on H
-- statement:
--   Let $h$ be a real number with $h>0$ and let $u,v\colon\mathfrak H\to\mathbb C$ be functions on the upper half-plane. Assume: the composite of `UpperHalfPlane.ofComplex` with $u$ is $h$-periodic as a function on $\mathbb C$ (since `ofComplex` is the identity on points of positive imaginary part and constant elsewhere, this amounts to $u(\tau+h)=u(\tau)$ for all $\tau\in\mathfrak H$); $u$ is holomorphic, in the sense of being differentiable as a map of complex manifolds from $\mathfrak H$ with its chart model $\mathcal I(\mathbb C)$ to $\mathbb C$; $u$ is bounded at $i\infty$, i.e. bounded along the filter `atImInfty`, so bounded on some region $\{\operatorname{Im}\tau\ge A\}$; for every $\tau\in\mathfrak H$ the complex-variable function obtained by composing `ofComplex` with $v$ has derivative $u(\tau)$ at the point $\tau$ of $\mathbb C$, so $v$ is a primitive of $u$ on $\mathfrak H$; and this same composite is $h$-periodic, i.e. $v(\tau+h)=v(\tau)$ on $\mathfrak H$. The conclusion is that $v$ too is bounded at $i\infty$.
--
--   This is the standard $q$-expansion argument showing that an $h$-periodic primitive of an $h$-periodic holomorphic function that is bounded at the cusp is itself bounded at the cusp: periodicity of the primitive forces the constant term of the $q$-expansion of $u$ to vanish. The periodicity of $v$ is essential ($u=1$, $v=\tau$ is a counterexample without it). It is used to establish boundedness at $i\infty$ of the evaluations of Eichler integrals, via [`HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval`](thm.html#HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold

theorem UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic {h : ℝ} (hh : 0 < h) {u v : UpperHalfPlane → ℂ}
    (hu_per : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) h) (hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hu_bdd : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : ∀ τ : UpperHalfPlane, HasDerivAt (v ∘ UpperHalfPlane.ofComplex) (u τ) ↑τ)
    (hv_per : Function.Periodic (v ∘ UpperHalfPlane.ofComplex) h) :
    UpperHalfPlane.IsBoundedAtImInfty v := by sorry
