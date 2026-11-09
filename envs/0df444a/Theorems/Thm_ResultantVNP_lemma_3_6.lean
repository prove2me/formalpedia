-- Prove2me | Theorems.Thm_ResultantVNP_lemma_3_6
-- name    : ResultantVNP.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:25:04.883603+00:00
-- url     : https://prove2.me/theorems/3f853f9f-f85b-4550-b08c-3a5a710b0c46
-- title:
--   Lemma 3.6 — constant grid labelings over $\mathbb F_3$
-- statement:
--   Let $m=3^r+1$ with $r\ge1$. If $b:\mathbb Z_m^2\to\mathbb F_3$ satisfies
--
--   $$
--   b_{ij}+b_{i-1,j}+b_{i,j-1}=0\qquad\text{for all }(i,j)\in\mathbb Z_m^2,
--   $$
--
--   then $b$ is constant.
--
--   Differences from the source:
--   - encoding: ℤ_m and 𝔽₃ → ZMod (3^r + 1) and ZMod 3; reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 3.6, Eq. (6), p.16

import Mathlib

namespace ResultantVNP

/-- **Lemma 3.6 (Constant grid labelings).** Let `m = 3^r + 1` with `r ≥ 1`. If `b : ℤ_m² → 𝔽₃`
satisfies `b_{ij} + b_{i−1,j} + b_{i,j−1} = 0` for all `(i, j) ∈ ℤ_m²`, then `b` is constant.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 3.6, Eq. (6), p.16.

**Formalization Note** `ℤ_m` is `ZMod m` and `𝔽₃` is `ZMod 3`. -/
theorem lemma_3_6 (r : ℕ) (hr : 1 ≤ r) (b : ZMod (3 ^ r + 1) × ZMod (3 ^ r + 1) → ZMod 3)
    (hb : ∀ i j, b (i, j) + b (i - 1, j) + b (i, j - 1) = 0) : ∀ p q, b p = b q := by sorry

end ResultantVNP
