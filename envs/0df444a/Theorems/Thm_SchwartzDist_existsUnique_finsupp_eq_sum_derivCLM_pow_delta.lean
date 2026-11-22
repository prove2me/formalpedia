-- Prove2me | Theorems.Thm_SchwartzDist_existsUnique_finsupp_eq_sum_derivCLM_pow_delta
-- name    : SchwartzDist.existsUnique_finsupp_eq_sum_derivCLM_pow_delta
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:44.381685+00:00
-- url     : https://prove2.me/theorems/fd5daf95-8c08-4b35-a477-dc8c1438ef57
-- title:
--   A tempered distribution on $\mathbb R$ supported at $0$ is $\sum_{k\le N}c_k\delta_0^{(k)}$, with unique coefficients
-- statement:
--   **Tempered distributions on $\mathbb R$ supported at the origin.** Let $T\in\mathcal S'(\mathbb R)$ be a complex tempered distribution whose support is contained in $\{0\}$. For $k\ge0$ let $\delta_0^{(k)}$ be the $k$-th distributional derivative of the Dirac distribution $\delta_0(\varphi)=\varphi(0)$, so that
--   $$\delta_0^{(k)}(\varphi)=(-1)^k\varphi^{(k)}(0)\qquad(\varphi\in\mathcal S(\mathbb R)).$$
--   Then there is a **unique** finitely supported sequence $(c_k)_{k\ge0}$ of complex numbers such that
--   $$T=\sum_{k\ge0}c_k\,\delta_0^{(k)}=\sum_{0\le k\le N}c_k\,\delta_0^{(k)},$$
--   where $N$ is any bound for the support of $(c_k)$.
--
--   Existence is the formula (5.3.2.1) of Theorem 5.3.2.1. Uniqueness is the linear independence of the $\delta_0^{(k)}$. Together they give the algebraic content of Theorem 5.3.2.1(1): $X^N\mapsto\frac1{N!}\delta_0^{(N)}$ is a linear isomorphism from $\mathbb C[X]$ onto the space of tempered distributions supported at $0$, which is the annihilator $\mathcal S_{00}(\mathbb R)^\perp$ of the Schwartz functions flat at $0$.
--
--   **Formalization Note.** The coefficient sequence is a `Finsupp` `c : ℕ →₀ ℂ`, and `c.sum` is the finite sum over its support. $\delta_0^{(k)}$ is `(TemperedDistribution.derivCLM ℂ ^ k) (TemperedDistribution.delta 0)`. Mathlib's `derivCLM` acts by $T\mapsto(\varphi\mapsto T(-\varphi'))$, which gives the sign convention displayed above. The support is Mathlib's `Distribution.dsupport`, and "supported at $0$" is encoded as $\subset\{0\}$, so that $T=0$ corresponds to $c=0$. The topological statement in 5.3.2.1(1), with its seminorms (5.3.2.2), is not part of this item; ERRATA F46 records that those seminorms do not give the finest locally convex topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 243, Theorem 5.3.2.1, (5.3.2.1) and the linear isomorphism $X^N\mapsto\frac1{N!}\delta_0^{(N)}$ of part (1); proof on p. 244; classical reference: L. Hörmander, The Analysis of Linear Partial Differential Operators I, Springer-Verlag, 1983, Ch. II, Thm. 2.3.4, p. 46 (as cited by the paper on p. 244)

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace SchwartzDist

theorem existsUnique_finsupp_eq_sum_derivCLM_pow_delta (T : 𝓢'(ℝ, ℂ))
    (hT : Distribution.dsupport (⇑T) ⊆ {(0 : ℝ)}) :
    ∃! c : ℕ →₀ ℂ, T = c.sum fun k a =>
      a • ((TemperedDistribution.derivCLM ℂ) ^ k) (TemperedDistribution.delta (0 : ℝ)) := by sorry

end SchwartzDist
