-- Prove2me | Theorems.Thm_ProdMixedTomo_theorem_4_7
-- name    : ProdMixedTomo.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:37.372541+00:00
-- url     : https://prove2.me/theorems/c34eb51a-cc09-4784-87ae-9f53272b6336
-- title:
--   Theorem 4.7 — $d_{\mathrm{tv}}(\mathrm{Bern}(\mu),\mathrm{Bern}(\nu))\le O(\min(1,\|\mu-\nu\|_\mu))$ for $\mu\le2/3$
-- statement:
--   Let $\pi=\mathrm{Bern}(\mu)$ and $\sigma=\mathrm{Bern}(\nu)$ be binary product distributions with mean vectors $\mu,\nu\in[0,1]^n$, and suppose $0\le\mu_i\le2/3$ for all $i$. Then for a universal constant $C$,
--   $$
--   d_{\mathrm{tv}}(\pi,\sigma)\ \le\ C\cdot\min\bigl(1,\ \|\mu-\nu\|_\mu\bigr).
--   $$
--   The test-set norm $\|\cdot\|_\mu$ therefore controls total variation between product distributions, including unbalanced ones where the $\ell_2$ distance of the means does not.
--
--   Differences from the source:
--   - encoding: O(·) / ≲ / Ω(·) → ∃ C > 0 chosen before n, μ and ν; reason: meaning of a universal constant (p.13)
--   - encoding: "Boolean product distributions with mean vectors μ, ν" → Bern(μ), Bern(ν) with ν ∈ [0,1]ⁿ (μ ∈ [0, 2/3]ⁿ from the hypothesis); reason: a product distribution on {0,1}ⁿ is determined by its mean vector (p.14)
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 4.7, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_TestNorms

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 4.7, p.24 (PDF p.26). If `π = Bern(μ)`, `σ = Bern(ν)` are binary product
distributions with `0 ≤ μᵢ ≤ 2/3` for all `i`, then `d_tv(π, σ) ≤ O(min(1, ‖μ − ν‖_μ))`. -/
theorem theorem_4_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (μ ν : Fin n → ℝ), (∀ i, 0 ≤ μ i ∧ μ i ≤ 2 / 3) →
      ν ∈ MeanBox n → dtv (bern μ) (bern ν) ≤ C * min 1 (vnorm μ (μ - ν)) := by sorry

end ProdMixedTomo
