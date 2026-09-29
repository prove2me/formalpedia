-- Prove2me | Theorems.Thm_Transcendence_expSum_first_nonvanishing
-- name    : Transcendence.expSum_first_nonvanishing
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:14.553756+00:00
-- url     : https://prove2.me/theorems/fed847b5-9f11-481c-86d6-09bccacd99ed
-- title:
--   First non-vanishing derivative of an exponential sum at the points 1, ..., m
-- statement:
--   Let $F(z) = \sum_i c_i\, e^{\rho_i z}$ be a finite exponential sum with distinct frequencies $\rho_i$ and coefficients $c_i$ not all zero. Suppose that for $j = 1, \dots, m$ all derivatives $F^{(k)}(j)$ with $k < n$ vanish. Then there are $r \ge n$ and $l_0 \in \{1, \dots, m\}$ such that $F^{(r)}(l_0) \ne 0$, while $F^{(k)}(j) = 0$ for every $j \in \{1, \dots, m\}$ and every $k < r$.
--
--   So $r$ is the first order at which some derivative at one of the points is non-zero. The sum is not identically zero because its frequencies are distinct (`FourExp.expPoly_ne_zero`), and a non-zero entire function has finite order at every point.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi); the step appears in the formalization of the Gelfond-Schneider theorem by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace Transcendence

theorem expSum_first_nonvanishing {ι : Type*} [Fintype ι] (c ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hc : c ≠ 0) (m n : ℕ) (hm : 0 < m)
    (hvan : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < n,
      iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (j : ℂ) = 0) :
    ∃ r l₀ : ℕ, n ≤ r ∧ 1 ≤ l₀ ∧ l₀ ≤ m ∧
      iteratedDeriv r (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (l₀ : ℂ) ≠ 0 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < r,
        iteratedDeriv k (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) (j : ℂ) = 0 := by
  sorry

end Transcendence
