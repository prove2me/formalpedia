-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_12_3_9_a
-- name    : RamanujanLostNotebook.PartIV.entry_12_3_9_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T14:34:15.039646+00:00
-- url     : https://prove2.me/theorems/91f6da40-adec-4496-8459-6e7ae8b83a10
-- title:
--   Ramanujan's formula for zeta(2r+1) (Lambert-series form)
-- statement:
--   Let $\alpha,\beta>0$ with $\alpha\beta=\pi^2$. Let $B_m$ be the Bernoulli numbers. For every integer $r\ge1$: $$(4\alpha)^{-r}\Big(\tfrac12\zeta(2r+1)+\sum_{m=1}^{\infty}\frac{1}{m^{2r+1}(e^{2m\alpha}-1)}\Big)-(-4\beta)^{-r}\Big(\tfrac12\zeta(2r+1)+\sum_{m=1}^{\infty}\frac{1}{m^{2r+1}(e^{2m\beta}-1)}\Big)=-\sum_{k=0}^{r+1}\frac{(-1)^kB_{2k}B_{2r+2-2k}}{(2k)!\,(2r+2-2k)!}\alpha^{r+1-k}\beta^k,$$ both series converging absolutely.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 12, Entry 12.3.9, p. 277, eq. (12.3.22).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem entry_12_3_9_a (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = Real.pi ^ 2)
    (r : ℕ) (hr : 1 ≤ r) :
    Summable (fun m : ℕ =>
      1 / (((m : ℝ) + 1) ^ (2 * r + 1) * (Real.exp (2 * ((m : ℝ) + 1) * α) - 1))) ∧
    Summable (fun m : ℕ =>
      1 / (((m : ℝ) + 1) ^ (2 * r + 1) * (Real.exp (2 * ((m : ℝ) + 1) * β) - 1))) ∧
    ((4 * α) ^ r)⁻¹ * ((riemannZeta (2 * (r : ℂ) + 1)).re / 2
          + ∑' m : ℕ,
              1 / (((m : ℝ) + 1) ^ (2 * r + 1) * (Real.exp (2 * ((m : ℝ) + 1) * α) - 1)))
        - ((-(4 * β)) ^ r)⁻¹ * ((riemannZeta (2 * (r : ℂ) + 1)).re / 2
          + ∑' m : ℕ,
              1 / (((m : ℝ) + 1) ^ (2 * r + 1) * (Real.exp (2 * ((m : ℝ) + 1) * β) - 1)))
      = -∑ k ∈ Finset.range (r + 2),
          (-1 : ℝ) ^ k * ((bernoulli (2 * k) : ℚ) : ℝ)
            * ((bernoulli (2 * (r + 1 - k)) : ℚ) : ℝ)
            * α ^ (r + 1 - k) * β ^ k
            / (((Nat.factorial (2 * k) : ℕ) : ℝ)
                * ((Nat.factorial (2 * (r + 1 - k)) : ℕ) : ℝ)) := by sorry
end RamanujanLostNotebook.PartIV
