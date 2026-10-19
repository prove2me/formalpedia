-- Prove2me | Theorems.Thm_QRHLittlewood_littlewood_two_sided_explicit
-- name    : QRHLittlewood.littlewood_two_sided_explicit
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:35:29.293823+00:00
-- url     : https://prove2.me/theorems/2dbb992a-be63-4d58-a323-7a935d48a1ae
-- title:
--   Explicit two-sided bound for $\log L(1,\chi)$ under $\Re s>7/8$ zero-freeness
-- statement:
--   Let $q\ge10^{100}$ and let $\chi$ be a primitive real Dirichlet character modulo $q$ such that $L(s,\chi)\neq0$ for every complex $s$ with $\Re s>7/8$. Then
--
--   $$|\log L(1,\chi)|\ \le\ \log\log\log q+3.2914,$$
--
--   so that $L(1,\chi)\le e^{3.2914}\log\log q$ and $L(1,\chi)\ge e^{-3.2914}/\log\log q$.
--
--   **Formalization Note** $\log$ is the principal complex logarithm; for a real character $L(1,\chi)$ is a positive real number, so this is the real logarithm.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, Certified harmonic-measure barriers and explicit Littlewood bounds from zero-free regions, https://doi.org/10.5281/zenodo.23400116, Theorem 2(i), $a=7/8$, $q\ge10^{100}$.

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Real

namespace QRHLittlewood

theorem littlewood_two_sided_explicit (q : ℕ) [NeZero q] (hq : (10 : ℝ) ^ 100 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ‖Complex.log (DirichletCharacter.LFunction χ 1)‖ ≤
      Real.log (Real.log (Real.log q)) + 32914 / 10000 := by sorry

end QRHLittlewood
