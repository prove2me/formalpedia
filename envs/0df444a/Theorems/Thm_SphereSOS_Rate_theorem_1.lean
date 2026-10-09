-- Prove2me | Theorems.Thm_SphereSOS_Rate_theorem_1
-- name    : SphereSOS.Rate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:21:07.23099+00:00
-- url     : https://prove2.me/theorems/d4550137-9350-41a5-abfb-d3adc478300e
-- title:
--   Theorem 1, p. 2 — $1\le\frac{p_\ell-p_{\min}}{p_{\max}-p_{\min}}\le1+(C_nd/\ell)^2$ for $\ell\ge C_nd$
-- statement:
--   For every $n\ge0$ there is a constant $C_n$, depending only on $n$, such that for every homogeneous polynomial $p(x_1,\dots,x_d)$ of degree $2n$ with $n\le d$ and every $\ell\ge C_nd$,
--   $$1\le\frac{p_\ell-p_{\min}}{p_{\max}-p_{\min}}\le1+\Big(\frac{C_nd}{\ell}\Big)^2,$$
--   where $p_{\max}$, $p_{\min}$ are the maximum and minimum of $p$ on $S^{d-1}$ and $p_\ell$ is the level-$\ell$ sum-of-squares upper bound.
--
--   The paper derives it from Theorem 2 applied to $F=(p_{\max}-p)/(p_{\max}-p_{\min})$. It answers the question of de Klerk and Laurent whether the upper-bound hierarchy converges at rate $O(1/\ell^2)$.
--
--   **Formalization Note** The level value is extended real to represent infeasible levels; this theorem supplies a real minimizing $p_\ell$ and its SOS certificate. The bound is stated cross-multiplied: $p_{\max}-p_{\min}\le p_\ell-p_{\min}\le(1+(C_nd/\ell)^2)(p_{\max}-p_{\min})$. This is equivalent to (2) when $p_{\max}>p_{\min}$, and remains meaningful when $p$ is constant on the sphere, where the printed ratio is $0/0$. The same constant $C_n$ appears in the level and in the bound, as printed.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 2, Theorem 1 and (2), with p_ℓ from §1.1

import Mathlib
import Definitions.Def_SphereSOS_Rate_Level

namespace SphereSOS.Rate

theorem theorem_1 :
    ∀ n : ℕ, ∃ C : ℝ, ∀ (d ℓ : ℕ) (p : MvPolynomial (Fin d) ℝ),
      n ≤ d →
      p.IsHomogeneous (2 * n) →
      C * (d : ℝ) ≤ (ℓ : ℝ) →
      ∃ pℓ : ℝ, pLevel d ℓ p = (pℓ : WithTop ℝ) ∧
        IsSosOnSphere ℓ
          (Matrix.of fun _ _ : Fin 1 => MvPolynomial.C pℓ - p) ∧
        pmax d p - pmin d p ≤ pℓ - pmin d p ∧
        pℓ - pmin d p ≤
          (1 + (C * (d : ℝ) / (ℓ : ℝ)) ^ 2) * (pmax d p - pmin d p) := by sorry

end SphereSOS.Rate
