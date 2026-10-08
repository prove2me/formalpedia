-- Prove2me | Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport
-- name    : ParameterizedCalculus.smooth_scalar_linear_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:38:30.051421+00:00
-- url     : https://prove2.me/theorems/ed7b461a-6a9a-4968-a61d-cc10b8f01248
-- title:
--   Smooth positive integrating factor for scalar linear transport
-- statement:
--   Let $P$ be a real normed vector space and let $q:\mathbb R\times P\to\mathbb R$ be jointly smooth. There is a jointly smooth function $\lambda:\mathbb R\times P\to\mathbb R$, strictly positive at every point and normalized by $\lambda(0,y)=1$, such that for every $y\in P$ and every real function $f$ satisfying the pointwise derivative equation
--
--   $$f'(t)=q(t,y)f(t)\qquad(0\le t\le1),$$
--
--   one has
--
--   $$f(t)=\lambda(t,y)f(0)\qquad(0\le t\le1).$$
--
--   The factor is independent of the chosen solution $f$. This parameter-dependent scalar transport result supplies the smooth positive conformal factor in the Moser argument and applies to any scalar linear evolution with a smooth coefficient. The derivative hypothesis includes the existence of the derivative at both endpoints.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed pp. 14–15, equations (2.1)–(2.2). Analytic consequence of the displayed logarithmic-derivative equation for λ_t, generalized to arbitrary normed parameter spaces; integrating factor exp(∫₀ᵗ q(s,y) ds).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped ContDiff

theorem ParameterizedCalculus.smooth_scalar_linear_transport
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : ℝ → P → ℝ)
    (hq : ContDiff ℝ ∞ (fun p : ℝ × P => q p.1 p.2)) :
    ∃ lam : ℝ → P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => lam p.1 p.2) ∧
      (∀ y, lam 0 y = 1) ∧ (∀ t y, 0 < lam t y) ∧
      ∀ y (f : ℝ → ℝ),
        (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (q t y * f t) t) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = lam t y * f 0 := by sorry
