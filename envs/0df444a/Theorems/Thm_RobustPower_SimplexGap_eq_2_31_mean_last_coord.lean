-- Prove2me | Theorems.Thm_RobustPower_SimplexGap_eq_2_31_mean_last_coord
-- name    : RobustPower.SimplexGap.eq_2_31_mean_last_coord
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:29:46.586765+00:00
-- url     : https://prove2.me/theorems/a9544d44-deb1-4ced-ae7c-21406a0da927
-- title:
--   Eqs. (2.31)–(2.32) — under the uniform measure on the simplex, E_µ[bₙ(ω)] = 1/(n+1)
-- statement:
--   Let $n\ge 3$ and let $(\Omega,\mu,b)$ be a scenario model in which $\mu$ is a probability measure, $b:\Omega\to\mathbb R^n$ is measurable, the uncertainty set $I_b(\Omega)$ is the corner simplex $\Delta_n=\{b\ge 0:\sum_j b_j\le1\}$, and $\mu$ is uniform on it: the law of $b$ under $\mu$ is Lebesgue measure on $\Delta_n$ divided by $\operatorname{vol}(\Delta_n)$. Then
--   $$\mathbb E_\mu[b_n(\omega)]=\frac{\int_{\Delta_n}x_n\,dx}{\operatorname{vol}(\Delta_n)}=\frac{1/(n+1)!}{1/n!}=\frac{1}{n+1}.$$
--
--   Combined with (2.30) this gives $z_{\mathrm{Stoch}}(b)\le 1/(n+1)$ on the instance of Theorem 2.6.
--
--   **Formalization Note** The $n$-th coordinate is index $n-1$ of `Fin n`; the expectation is the Bochner integral $\int b_{n}\,d\mu$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 20, proof of Theorem 2.6, Eqs. (2.31)–(2.32)

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

namespace RobustPower.SimplexGap

open MeasureTheory

/-- Eqs. (2.31)–(2.32): under the uniform probability measure on the corner simplex, the mean of
the last coordinate is `E_μ[bₙ(ω)] = 1/(n+1)`. -/
theorem eq_2_31_mean_last_coord (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    ∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ = 1 / ((n : ℝ) + 1) := by sorry

end RobustPower.SimplexGap
