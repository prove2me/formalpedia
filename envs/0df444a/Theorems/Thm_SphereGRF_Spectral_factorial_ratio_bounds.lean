-- Prove2me | Theorems.Thm_SphereGRF_Spectral_factorial_ratio_bounds
-- name    : SphereGRF.Spectral.factorial_ratio_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:03.623608+00:00
-- url     : https://prove2.me/theorems/91d9c33c-3856-4e96-8428-df7509a20335
-- title:
--   Proof of Theorem 3.1, p. 13 — $c_1(n)\ell^{2n} \le \frac{(\ell+n)!}{(\ell-n)!} \le c_2(n)\ell^{2n}$ for $n \le \ell$
-- statement:
--   For every $n \in \mathbb N_0$ there are constants $c_1(n), c_2(n) > 0$ such that for all $\ell \in \mathbb N_0$ with $n \le \ell$,
--
--   $$
--   c_1(n)\,\ell^{2n} \le \frac{(\ell+n)!}{(\ell-n)!} \le c_2(n)\,\ell^{2n}.
--   $$
--
--   The ratio $(\ell+n)!/(\ell-n)!$ is the squared weighted norm of $P_\ell^{(n)}$ up to the factor $2/(2\ell+1)$; the bound converts the weighted Parseval identity into the polynomial weight $\ell^{2n}$ of the sequence space $\ell_n$.
--
--   **Formalization Note** $\ell^{2n}$ is a natural power with $0^0 = 1$, so the case $\ell = n = 0$ reads $c_1 \le 1 \le c_2$. The constants are chosen before $\ell$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, proof of Theorem 3.1, p. 13, display following 'there exist constants c1(n) and c2(n) such that'

import Mathlib

namespace SphereGRF.Spectral

/-- Proof of Theorem 3.1, p. 13: for every `n` there are `c₁(n), c₂(n) > 0` with
`c₁(n) ℓ^{2n} ≤ (ℓ+n)!/(ℓ−n)! ≤ c₂(n) ℓ^{2n}` for all `ℓ ≥ n`. -/
theorem factorial_ratio_bounds (n : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ℓ : ℕ, n ≤ ℓ →
      c₁ * (ℓ : ℝ) ^ (2 * n) ≤ ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ∧
      ((ℓ + n).factorial : ℝ) / ((ℓ - n).factorial : ℝ) ≤ c₂ * (ℓ : ℝ) ^ (2 * n) := by sorry

end SphereGRF.Spectral
