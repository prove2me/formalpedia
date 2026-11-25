-- Prove2me | Theorems.Thm_UpperHalfPlane_integral_im_rpow_div_norm_sub_conj_rpow
-- name    : UpperHalfPlane.integral_im_rpow_div_norm_sub_conj_rpow
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:17:28.2038+00:00
-- url     : https://prove2.me/theorems/051ab1d4-09b6-41a5-a422-3b7e791d47bb
-- title:
--   Selberg-type kernel integral on the upper half-plane: $\int_{\mathbb H} y^\sigma / |z - \bar w|^{2\sigma}\, d\mu(z) = 4\pi / ((\sigma - 1)(4\,\mathrm{Im}\, w)^\sigma)$ for $\sigma > 1$
-- statement:
--   Let $\mathbb H = \{z \in \mathbb C : \mathrm{Im}\, z > 0\}$ carry the hyperbolic (invariant) measure $d\mu(z) = \frac{dx\, dy}{y^2}$, $z = x + iy$. Fix $w \in \mathbb H$ and a real number $\sigma > 1$. Then the function
--
--   $$z \mapsto \frac{(\mathrm{Im}\, z)^\sigma}{|z - \bar w|^{2\sigma}}$$
--
--   is integrable on $\mathbb H$ for $\mu$, and
--
--   $$\int_{\mathbb H} \frac{(\mathrm{Im}\, z)^\sigma}{|z - \bar w|^{2\sigma}}\, d\mu(z) = \frac{4\pi}{(\sigma - 1)\,(4\, \mathrm{Im}\, w)^\sigma}.$$
--
--   For example, for $\sigma = 2$ and $w = i$ the integral equals $\pi/4$. Since $|z - \bar w|^2 = |z - w|^2 + 4\,\mathrm{Im}\, z\,\mathrm{Im}\, w$, the integrand is $(4\,\mathrm{Im}\, w)^{-\sigma}\,(1 + u(z,w))^{-\sigma}$ with $u(z,w) = |z-w|^2/(4\,\mathrm{Im}\, z\,\mathrm{Im}\, w)$ the point-pair invariant, so this is the Selberg transform of $(1+u)^{-\sigma}$; it is finite exactly when $\sigma > 1$.
--
--   Role: for $\sigma = k/2$ the integrand dominates the weight-$k$ Bergman reproducing integrand of a function with $|f(z)|\,(\mathrm{Im}\, z)^{k/2}$ bounded (for instance a cusp form), so for $k \ge 3$ it gives the absolute convergence of the weight-$k$ Bergman reproducing integral on $\mathbb H$.
--
--   **Formalization Note**: `UpperHalfPlane` is Mathlib's upper half-plane and its `MeasureSpace` instance (`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`) is the invariant measure $dx\,dy/y^2$, so the unqualified `MeasureTheory.Integrable` and `∫ z : UpperHalfPlane, ...` refer to $\mu$. `starRingEnd ℂ` is complex conjugation, `‖·‖` is the complex absolute value, and the powers `^ σ`, `^ (2 * σ)` are real powers (`Real.rpow`) of positive reals.
-- source:
--   H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Sections 1.8 and 2.3 (point-pair invariants); H. Iwaniec, Topics in Classical Automorphic Forms, Graduate Studies in Mathematics 17, AMS 1997, Section 3.2 (reproducing kernels)

import Mathlib

set_option autoImplicit false

theorem UpperHalfPlane.integral_im_rpow_div_norm_sub_conj_rpow (w : UpperHalfPlane) (σ : ℝ) (hσ : 1 < σ) :
    MeasureTheory.Integrable
        (fun z : UpperHalfPlane => z.im ^ σ / ‖(z : ℂ) - starRingEnd ℂ (w : ℂ)‖ ^ (2 * σ)) ∧
      ∫ z : UpperHalfPlane, z.im ^ σ / ‖(z : ℂ) - starRingEnd ℂ (w : ℂ)‖ ^ (2 * σ) =
        4 * Real.pi / ((σ - 1) * (4 * w.im) ^ σ) := by
  sorry
