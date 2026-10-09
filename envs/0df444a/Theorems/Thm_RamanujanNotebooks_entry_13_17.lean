-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_13_17
-- name    : RamanujanNotebooks.entry_13_17
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T03:11:24.893248+00:00
-- url     : https://prove2.me/theorems/21961b38-7b6a-47c8-8f3d-a6a423ee4825
-- title:
--   The Abel–Plana summation formula on a finite range of integers
-- statement:
--   Let $a\le n$ be nonnegative integers and let $\varphi$ be analytic at every point of the strip $a\le\operatorname{Re}z\le n$, with $|\varphi(x\pm iy)|e^{-2\pi y}\to0$ as $y\to\infty$ uniformly for $a\le x\le n$. Assume that $u\mapsto\frac{\varphi(n+iu)-\varphi(n-iu)-\varphi(a+iu)+\varphi(a-iu)}{e^{2\pi u}-1}$ is integrable on $(0,\infty)$. Then $$\sum_{k=a}^n\varphi(k)=\int_a^n\varphi(u)\,du+\tfrac12\{\varphi(a)+\varphi(n)\}-i\int_0^\infty\frac{\varphi(n+iu)-\varphi(n-iu)-\varphi(a+iu)+\varphi(a-iu)}{e^{2\pi u}-1}du.$$ Differs from the printed source: the integrability of the last integrand is added by us.
--
--   **Discrepancy from the printed source.** Book, pp. 220–221: φ analytic for a ≤ Re z ≤ n and lim_{y→∞} |φ(x ± iy)| e^{-2πy} = 0 uniformly for a ≤ x ≤ n; no condition on the integral over (0, ∞). Our statement adds the integrability of the combined integrand (φ(n+iu) − φ(n−iu) − φ(a+iu) + φ(a−iu))/(e^{2πu} − 1) on (0, ∞) (the growth condition alone does not give it), reads 'analytic on the closed strip' as analytic at each of its points, and writes the uniform limit with ε and Y. Additions by us (the book's Lemma of Section 18 carries the analogous proviso 'provided that the integrals below exist').
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part II (Springer, 1989), Chapter 13, Entry 17, p. 220, eq. (17.1).

import Mathlib

namespace RamanujanNotebooks
theorem entry_13_17 (φ : ℂ → ℂ) (a n : ℕ) (han : a ≤ n)
    (hφ : ∀ z : ℂ, (a : ℝ) ≤ z.re → z.re ≤ (n : ℝ) → AnalyticAt ℂ φ z)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (n : ℝ) →
      ‖φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ * Real.exp (-(2 * Real.pi * y)) ≤ ε ∧
      ‖φ ((x : ℂ) - (y : ℂ) * Complex.I)‖ * Real.exp (-(2 * Real.pi * y)) ≤ ε)
    (hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => (φ ((n : ℂ) + (u : ℂ) * Complex.I) - φ ((n : ℂ) - (u : ℂ) * Complex.I)
          - φ ((a : ℂ) + (u : ℂ) * Complex.I) + φ ((a : ℂ) - (u : ℂ) * Complex.I))
          / ((Real.exp (2 * Real.pi * u) : ℂ) - 1)) (Set.Ioi (0 : ℝ))) :
    ∑ k ∈ Finset.Icc a n, φ (k : ℂ)
      = (∫ u in (a : ℝ)..(n : ℝ), φ (u : ℂ)) + (φ (a : ℂ) + φ (n : ℂ)) / 2
        - Complex.I * ∫ u in Set.Ioi (0 : ℝ),
            (φ ((n : ℂ) + (u : ℂ) * Complex.I) - φ ((n : ℂ) - (u : ℂ) * Complex.I)
              - φ ((a : ℂ) + (u : ℂ) * Complex.I) + φ ((a : ℂ) - (u : ℂ) * Complex.I))
            / ((Real.exp (2 * Real.pi * u) : ℂ) - 1) := by sorry
end RamanujanNotebooks
