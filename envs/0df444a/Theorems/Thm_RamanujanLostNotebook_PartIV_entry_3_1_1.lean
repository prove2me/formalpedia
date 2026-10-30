-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_3_1_1
-- name    : RamanujanLostNotebook.PartIV.entry_3_1_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T15:15:51.546244+00:00
-- url     : https://prove2.me/theorems/439b3893-a3b0-4925-bb65-db66a7645d3c
-- title:
--   Guinand's formula (Ramanujan's generalisation of Koshliakov's formula)
-- statement:
--   Let $\alpha,\beta>0$ with $\alpha\beta=\pi^2$ and let $\sigma_{-s}(n)=\sum_{d\mid n}d^{-s}$. For complex $s$ with $s\ne\pm1$ and $s$ not an even integer, both series converge absolutely and $\sqrt{\alpha}\sum_{n\ge1}\sigma_{-s}(n)n^{s/2}K_{s/2}(2n\alpha)-\sqrt{\beta}\sum_{n\ge1}\sigma_{-s}(n)n^{s/2}K_{s/2}(2n\beta)$$=\tfrac14\Gamma(\tfrac s2)\zeta(s)\{\beta^{(1-s)/2}-\alpha^{(1-s)/2}\}+\tfrac14\Gamma(-\tfrac s2)\zeta(-s)\{\beta^{(1+s)/2}-\alpha^{(1+s)/2}\}$. Differs from the printed source: the book allows every complex s; we exclude s = +-1 and the even integers, where the printed right side is a pole or a pole-times-zero form (numerical evidence, not a proof; restriction ours); the even integers other than 0 are covered by entry_3_1_1_completed. The independent audit confirmed this difference (its own numerics; not a proof).
--
--   **Discrepancy from the printed source.** Book, pp. 94-95 (3.1.5) and pp. 96-97 (3.3.1): 'if s is any complex number'. Stated here: s != 1, s != -1, s not an even integer. Reason: at s = 0, +-1 a factor of the printed right side has a pole (only limits make sense; they are Entries 3.3.3 and 3.3.2); at nonzero even s one of Gamma(+-s/2) zeta(+-s) is pole times trivial zero, and Lean's Gamma is 0 at poles, so the literal Lean right side is wrong there (numeric: alpha=0.3, s=2: left side 2.19117325..., literal Lean right side -0.67910952...). Evidence: numerical (45 digits), not a proof; the analytic statement for all s is the book's. Who: the restriction is ours. Independent audit (Codex): confirms the restriction; its own values at alpha=0.3, s=2: literal Lean right side -0.679109529898585264595671221698 (same as ours); at alpha=1, s=0.7+1.3i and alpha=4.5, s=-3.3 both sides agree with ours. Adjudicated value (third computation, 110 digits, 600 terms, two routes for K): Bessel side = completed-zeta right side = 2.191173252187051798064765798434386442802, gap to the literal right side 2.870282782085637062660437020132727802805. The audit's printed Bessel-side value 2.19117325218704956... was the 60-term partial sum of the series (truncation error 2.2e-15), not the limit, and is withdrawn.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 3, Entry 3.1.1, p. 94, eq. (3.1.5).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_besselKC

namespace RamanujanLostNotebook.PartIV
theorem entry_3_1_1 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = Real.pi ^ 2)
    (s : ℂ) (hs1 : s ≠ 1) (hs1' : s ≠ -1) (hs : ∀ k : ℤ, s ≠ 2 * (k : ℂ)) :
    ∃ A B : ℂ,
      HasSum (fun n : ℕ =>
        (∑ d ∈ Nat.divisors (n + 1), (d : ℂ) ^ (-s)) * ((n : ℂ) + 1) ^ (s / 2)
          * RamanujanLostNotebook.PartIV.besselKC (s / 2) ((2 * ((n : ℝ) + 1) * α : ℝ) : ℂ)) A ∧
      HasSum (fun n : ℕ =>
        (∑ d ∈ Nat.divisors (n + 1), (d : ℂ) ^ (-s)) * ((n : ℂ) + 1) ^ (s / 2)
          * RamanujanLostNotebook.PartIV.besselKC (s / 2) ((2 * ((n : ℝ) + 1) * β : ℝ) : ℂ)) B ∧
      ((Real.sqrt α : ℝ) : ℂ) * A - ((Real.sqrt β : ℝ) : ℂ) * B =
        1 / 4 * Complex.Gamma (s / 2) * riemannZeta s
            * ((β : ℂ) ^ ((1 - s) / 2) - (α : ℂ) ^ ((1 - s) / 2))
          + 1 / 4 * Complex.Gamma (-s / 2) * riemannZeta (-s)
            * ((β : ℂ) ^ ((1 + s) / 2) - (α : ℂ) ^ ((1 + s) / 2)) := by sorry
end RamanujanLostNotebook.PartIV
