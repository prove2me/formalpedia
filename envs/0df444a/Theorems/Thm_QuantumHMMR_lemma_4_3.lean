-- Prove2me | Theorems.Thm_QuantumHMMR_lemma_4_3
-- name    : QuantumHMMR.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:28.05323+00:00
-- url     : https://prove2.me/theorems/4d315342-95d2-4844-b97b-250d86e5bc6c
-- title:
--   Lemma 4.3 — a power sum bounded by its first $D$ values
-- statement:
--   Let $D \ge 1$ and $0 < \rho < 1$. Suppose
--   $$
--   u_j = \sum_{i=1}^D b_i \lambda_i^j \quad (j \ge 1), \qquad |\lambda_i| \le \rho.
--   $$
--   If $|u_1|, \dots, |u_D| \le B$, then for every $j \ge D$
--   $$
--   |u_j| \le B \cdot D \cdot 2^D \binom{j + D - 2}{D - 1} \rho^{j - D}. \tag{15}
--   $$
--
--   The bound controls a finite spectral expansion from its first few values, without bounding the coefficients $b_i$ individually, which would introduce a dependence on the dimension.
--
--   Differences from the source:
--   - reading: b_i, λ_i of unspecified type → complex numbers b_i, λ_i; reason: the eigenvalues of a moment operator are complex in general; complex covers real
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.3, Eq. (15), p.13

import Mathlib

namespace QuantumHMMR

/-- **Lemma 4.3** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Eq. (15), p.13). Let `D ≥ 1` and `0 < ρ < 1`. Suppose
`u_j = Σ_{i=1}^{D} b_i λ_i^j` for `j ≥ 1`, with `|λ_i| ≤ ρ`. If `|u_1|, …, |u_D| ≤ B`, then for every
`j ≥ D`, `|u_j| ≤ B · D · 2^D · C(j + D - 2, D - 1) · ρ^{j-D}`.

**Formalization Note** `b_i, λ_i` are complex numbers, indexed by `Fin D`. The natural-number
subtractions `j + D - 2`, `D - 1`, `j - D` are exact under `D ≥ 1`, `j ≥ D`. -/
theorem lemma_4_3 (D : ℕ) (hD : 1 ≤ D) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (b lam : Fin D → ℂ) (hlam : ∀ i, ‖lam i‖ ≤ ρ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i, b i * lam i ^ j‖ ≤ B) :
    ∀ j : ℕ, D ≤ j →
      ‖∑ i, b i * lam i ^ j‖ ≤ B * D * 2 ^ D * ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by sorry

end QuantumHMMR
