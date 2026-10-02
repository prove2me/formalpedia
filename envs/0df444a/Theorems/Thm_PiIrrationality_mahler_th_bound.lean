-- Prove2me | Theorems.Thm_PiIrrationality_mahler_th_bound
-- name    : PiIrrationality.mahler_th_bound
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-02T00:02:31.64486+00:00
-- url     : https://prove2.me/theorems/4c5e26d8-763a-4d48-8ed4-7db4715881c7
-- title:
--   Mahler (1953), §2 formula (4): the auxiliary sum bound ‖Th(x,y)‖ < 2^m·m·max‖A_hk(x)‖
-- statement:
--   This is Mahler's auxiliary sum estimate, §2 formula (4) of "On the approximation of π" (1953), with the §1 auxiliary data taken as explicit hypotheses.
--
--   Let m ≥ 2 and let A_hk(x) be the §1 auxiliary polynomials, evaluated at a complex point x with ‖log x‖ < 2. Mahler's size bound (b) is taken as the explicit hypothesis that a uniform bound maxA > 0 satisfies ‖A_hk(x)‖ ≤ maxA for all indices h, k ≤ m whenever ‖log x‖ < 2. The auxiliary sums are T_h(x, y) = Σ_{k<m} A_hk(x)·ψ_hk(y), where the y-multipliers satisfy ‖ψ_hk(y)‖ < 2^m for ‖y‖ < 2.
--
--   Then for ‖log x‖ < 2 and ‖y‖ < 2, each auxiliary sum satisfies ‖T_h(x, y)‖ < 2^m · m · maxA, by the triangle inequality over the m-term sum — an elementary complex estimate, provable once stated, with no transcendence input beyond the hypotheses. The deep content (existence of the A_hk with the §1 properties (a)–(c)) stays inside the hypotheses.
-- source:
--   K. Mahler, On the approximation of π, Nederl. Akad. Wetensch. Proc. Ser. A 56 = Indag. Math. 15 (1953), 30–42, §2, formula (4). Reprint: https://content.ems.press/assets/public/full-texts/books/252/chapters/online-pdf/252-chapter-4986.pdf

import Mathlib

namespace PiIrrationality

theorem mahler_th_bound (m : ℕ) (hm : 2 ≤ m)
    (A : ℕ → ℕ → ℂ → ℂ)
    (ψ : ℕ → ℕ → ℂ → ℂ)
    (Th : ℕ → ℂ → ℂ → ℂ)
    (hTh : ∀ h x y, h ≤ m →
      Th h x y = Finset.sum (Finset.range m) (fun k => A h k x * ψ h k y))
    (hψ : ∀ h k y, h ≤ m → k < m → ‖y‖ < 2 →
      ‖ψ h k y‖ < 2 ^ m)
    (maxA : ℝ) (hmaxA : 0 < maxA)
    (hbound : ∀ h k x, h ≤ m → k ≤ m →
      ‖Complex.log x‖ < 2 → ‖A h k x‖ ≤ maxA)
    (x y : ℂ) (h : ℕ) (hh : h ≤ m)
    (hlog : ‖Complex.log x‖ < 2)
    (hy : ‖y‖ < 2) :
    ‖Th h x y‖ < 2 ^ m * (m : ℝ) * maxA := by sorry

end PiIrrationality
