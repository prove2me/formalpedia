-- Prove2me | Theorems.Thm_RSCapacity_equation_34
-- name    : RSCapacity.equation_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:50.83514+00:00
-- url     : https://prove2.me/theorems/e636f4fe-d80b-4006-b687-61f9221b6d11
-- title:
--   Equation (34): $\operatorname{rank}\Phi_{\alpha,y}\le(m^3/r+m^2)\Lambda(W+m)\le(2m^3/r)\Lambda(W+m)$
-- statement:
--   Fix integers $1\le r<K\le A$, reals $1<c<s<A/(K-1)$, set $m=r^3$ and let $W,\mathcal T,\mathcal Q$ be as in §4.1. For every field $F$ and every $(\alpha,y)\in F^2$, the map $\Phi_{\alpha,y}$ recording the local constraints on $\mathcal Q$ satisfies
--   $$\operatorname{rank}\Phi_{\alpha,y}\ \le\ \Bigl(\frac{m^3}{r}+m^2\Bigr)\Lambda(W+m)\ \le\ \frac{2m^3}{r}\,\Lambda(W+m).$$
--
--   This is the rank side of the dimension–rank comparison: one incidence imposes at most this many independent linear conditions, independently of $(\alpha,y)$ and of the characteristic.
--
--   Differences from the source:
--   - generalization: in the proof of Lemma 4.5, whose statement is for all sufficiently large r → every r ≥ 1; reason: the counting argument uses only that m/r is an integer and m² ≤ m³/r, both true for m = r³ and r ≥ 1
--   - encoding: m³/r, m² and 2m³/r with m = r³ → the natural numbers r⁸, r⁶ and 2r⁸; reason: exact for m = r³
--   - encoding: rank Φ_{α,y} → Module.rank of the image, a cardinal; reason: no instance changes; an infinite-dimensional image would not read as 0
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Equation (34), proof of Lemma 4.5, p.17 (PDF 19); setting of Lemma 4.5, p.16 (PDF 18)

import Mathlib
import Definitions.Def_RSCapacity_LocalConstraints

set_option autoImplicit false

namespace RSCapacity

/-- **Equation (34) (the local rank count).** Jeronimo, arXiv:2609.05870 (held version of
November 1, 2026, sha256 9a0069bd…), proof of Lemma 4.5, p.17 (PDF 19), in the setting of
Lemma 4.5, p.16 ("Fix 1 < c < s, set m = r³, and define W, 𝒯 as above"):
rank Φ_{α,y} ≤ (m³/r + m²) Λ(W + m) ≤ (2m³/r) Λ(W + m).

**Formalization Note.** m = r³, so m³/r = r⁸, m² = r⁶ and 2m³/r = 2r⁸ are natural numbers.
Holds for every r ≥ 1, every field F and every (α, y) ∈ F² under the standing hypotheses of §4.1
(1 ≤ r < K ≤ A, 1 < c < s < A/(K − 1)). rank Φ_{α,y} is the dimension of the range of Φ_{α,y} on
𝒬, as a cardinal. -/
theorem equation_34 {F : Type*} [Field F] (A K r : ℕ) (c s : ℝ) (hr : 1 ≤ r) (hrK : r < K)
    (hKA : K ≤ A) (hc : 1 < c) (hcs : c < s) (hsu : s < (A : ℝ) / ((K : ℝ) - 1)) (α y : F) :
    rankPhi F A K r (r ^ 3) c s α y ≤
        (((r ^ 8 + r ^ 6) * Lambda r ((Wcut r (r ^ 3) c + r ^ 3 : ℕ) : ℝ) : ℕ) : Cardinal) ∧
      (r ^ 8 + r ^ 6) * Lambda r ((Wcut r (r ^ 3) c + r ^ 3 : ℕ) : ℝ) ≤
        2 * r ^ 8 * Lambda r ((Wcut r (r ^ 3) c + r ^ 3 : ℕ) : ℝ) := by sorry

end RSCapacity
