-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_14_21_i
-- name    : RamanujanNotebooks.entry_14_21_i
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T03:07:14.511552+00:00
-- url     : https://prove2.me/theorems/1f1f2119-e844-4b9b-b565-937b82ad0eac
-- title:
--   Ramanujan's formula for zeta(2n+1)
-- statement:
--   Let $\alpha,\beta>0$ with $\alpha\beta=\pi^2$ and $n$ a non-zero integer. Then $$\alpha^{-n}\Big\{\frac12\zeta(2n+1)+\sum_{k\ge1}\frac{k^{-2n-1}}{e^{2\alpha k}-1}\Big\}=(-\beta)^{-n}\Big\{\frac12\zeta(2n+1)+\sum_{k\ge1}\frac{k^{-2n-1}}{e^{2\beta k}-1}\Big\}-2^{2n}\sum_{k=0}^{n+1}(-1)^k\frac{B_{2k}}{(2k)!}\frac{B_{2n+2-2k}}{(2n+2-2k)!}\alpha^{n+1-k}\beta^k$$ (the finite sum is empty for $n\le-2$).
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part II (Springer, 1989), Chapter 14, Entry 21(i), p. 275.

import Mathlib

namespace RamanujanNotebooks
theorem entry_14_21_i (α β : ℝ) (n : ℤ) (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α * β = Real.pi ^ 2) (hn : n ≠ 0) :
    ∃ S T : ℝ,
      HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (-(2 * n + 1)) /
        (Real.exp (2 * α * ((k : ℝ) + 1)) - 1)) S ∧
      HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (-(2 * n + 1)) /
        (Real.exp (2 * β * ((k : ℝ) + 1)) - 1)) T ∧
      α ^ (-n) * ((riemannZeta (2 * (n : ℂ) + 1)).re / 2 + S) =
        (-β) ^ (-n) * ((riemannZeta (2 * (n : ℂ) + 1)).re / 2 + T)
          - (2 : ℝ) ^ (2 * n) * ∑ k ∈ Finset.range (n + 2).toNat,
              (-1 : ℝ) ^ k * (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
                (bernoulli (2 * n + 2 - 2 * (k : ℤ)).toNat : ℝ) /
                (Nat.factorial (2 * n + 2 - 2 * (k : ℤ)).toNat : ℝ) *
                α ^ (n + 1 - (k : ℤ)) * β ^ k := by sorry
end RamanujanNotebooks
