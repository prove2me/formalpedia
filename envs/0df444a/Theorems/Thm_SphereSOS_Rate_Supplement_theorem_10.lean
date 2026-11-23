-- Prove2me | Theorems.Thm_SphereSOS_Rate_Supplement_theorem_10
-- name    : SphereSOS.Rate.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:06:51.81124+00:00
-- url     : https://prove2.me/theorems/ab9b59ae-92e1-467c-8d53-bde45d89b210
-- title:
--   Theorem 10 (companion theorem; not used in the proof of the goal) — tightness of the kernel approximation rate
-- statement:
--   Let $d\ge2$ and $\ell\ge0$ be integers. For a real univariate polynomial $q$ of degree at most $\ell$, let $\lambda_i(q^2)$ be its square's Gegenbauer coefficient in the sphere normalization of (9), and require $\lambda_0(q^2)=1$. Write $\rho_2(d,\ell)$ for the infimum of $|\lambda_2(q^2)^{-1}-1|$ over these polynomials, with cost $+\infty$ when $\lambda_2(q^2)=0$.
--
--   There are absolute constants $C>0$ and $a>0$ such that, simultaneously for every integer $d\ge2$ and every integer $\ell$ satisfying $a d\le\ell$,
--
--   $$
--   \rho_2(d,\ell)\ge C\left(\frac d\ell\right)^2.
--   $$
--
--   This gives a matching lower rate for the specific kernel approximation quantity in the quadratic case. It is a companion to the mission's goal, Theorem 2, and is not used in that goal's proof. It does not assert an integrality gap for the sum-of-squares hierarchy. Both constants are independent of dimension and level.
--
--   Differences from the source:
--
--   - encoding: integer sphere dimension in the Gegenbauer setting of §2 → d : ℕ with 2 ≤ d, including d = 2; reason: the weight exponent is (d−3)/2; d ≥ 2 is the standing sphere domain, including the integrable circle case
--   - reading: ℓ ≥ Ω(d) → there is an absolute a > 0 such that a*d ≤ ℓ, with both C and a quantified before d and ℓ; reason: Theorem 10 and its root-gap estimate on p. 10 are uniform in the same linear-threshold regime; no numerical constants are specified
--   - reading: ρ₂ of (10), used through (13) and (14) → the published rho d 1 ℓ, using degree at most ℓ and the single k = 1 summand; reason: (10) prints a sum to 2n and exact degree, whereas (13) uses the n-term coefficient-vector optimization over degrees at most ℓ; the paragraph before (14) explicitly says there is simply one term for 2n = 2
--   - encoding: ρ₂ ≥ C(d/ℓ)² with inverse-distance cost → ENNReal.ofReal (C*((d:ℝ)/(ℓ:ℝ))^2) ≤ rho d 1 ℓ, with cost +∞ at a zero coefficient; reason: the published extended nonnegative infimum retains divergent inverse costs; positivity of C, a and d and the threshold imply ℓ > 0 and a strictly positive finite left side
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 10, Theorem 10; governing definitions §2, pp. 5–6, (9), and p. 8, (13)–(14).

import Mathlib
import Definitions.Def_SphereSOS_Rate_Rho

namespace SphereSOS.Rate.Supplement

/-- Fang–Fawzi, arXiv:1908.05155v1, Theorem 10, p. 10.
The quadratic kernel error has a uniform positive lower bound of order `(d / ℓ)^2`
above an absolute linear threshold. Both constants precede dimension and level;
`rho d 1 ℓ` is the published extended-nonnegative-real version of `ρ₂(d, ℓ)`.
The sphere domain includes `d = 2`. -/
theorem theorem_10 :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ d ℓ : ℕ, 2 ≤ d → a * (d : ℝ) ≤ (ℓ : ℝ) →
        ENNReal.ofReal (C * ((d : ℝ) / (ℓ : ℝ)) ^ 2) ≤
          SphereSOS.Rate.rho d 1 ℓ := by sorry

end SphereSOS.Rate.Supplement
