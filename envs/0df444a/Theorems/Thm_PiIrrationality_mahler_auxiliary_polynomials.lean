-- Prove2me | Theorems.Thm_PiIrrationality_mahler_auxiliary_polynomials
-- name    : PiIrrationality.mahler_auxiliary_polynomials
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-02T04:19:33.194071+00:00
-- url     : https://prove2.me/theorems/940cb9f0-bc82-41df-9f02-027bee097b1d
-- title:
--   Mahler (1953), §1 Lemma at m=10: 121 integral auxiliary polynomials, det ≠ 0, bounds (b) and (c)
-- statement:
--   This is the §1 Lemma of Mahler's "On the approximation of π" (1953), specialized to m = 10 — the deep transcendence input to the whole paper. It is proved in Mahler's companion paper "On the approximation of logarithms of algebraic numbers" (Phil. Trans. Roy. Soc. London A 245 (1953), 371–398, Theorem 1) by a Siegel-lemma / Padé-approximation construction for e^x; nothing of that machinery exists in Mathlib.
--
--   For n ≥ 50 (the paper's §3 regime, where the lemma's hypothesis (1), m+1 > 2|log x|, holds at the point x = i used in §2 since |log i| = π/2 < 11/2), there exist (m+1)² = 121 polynomials A_hk (h,k = 0,…,10) with rational integral coefficients, each of degree at most n, such that:
--
--   (a) the determinant D(x) = det(A_hk(x)) does not vanish identically;
--
--   (b) for every complex x, ‖A_hk(x)‖ ≤ 10! · 2^{10−3n/2} · (n+1)^{21} · (√32)^{11n} · (1 + ‖x‖ + ⋯ + ‖x‖^n);
--
--   (c) the 11 remainder functions R_h(x) = Σ_{k=0}^{10} A_hk(x)·(log x)^k satisfy, for x ≠ 0,1 with ‖log x‖ < 11/2: ‖R_h(x)‖ ≤ 10! · 2^{−3n/2} · (e√n)^{11} · e^{(2n+1)‖log x‖} · (‖x‖/11)^n.
--
--   The polynomials are formalized as Polynomial ℤ (integral coefficients); evaluation at complex points goes through the canonical ring hom ℤ →+* ℂ. Bound (b) is the value form used in §3 — max ‖A_hk(x)‖ feeds the §2 auxiliary-sum estimate of the sibling node mahler_th_bound. Bound (c) is the remainder estimate decaying exponentially in n that drives §§3–4. Decomposition child A of PiIrrationality.mahler_1953_eq13 (see ~/workspace/p2m_harness/mahler_pi_triage.md §3); stated with a single sorry.
-- source:
--   K. Mahler, On the approximation of π, Nederl. Akad. Wetensch. Proc. Ser. A 56 = Indag. Math. 15 (1953), 30–42, §1 Lemma. Reprint: https://content.ems.press/assets/public/full-texts/books/252/chapters/online-pdf/252-chapter-4986.pdf . Proved in K. Mahler, On the approximation of logarithms of algebraic numbers, Phil. Trans. Roy. Soc. London A 245 (1953), 371–398, Theorem 1.

import Mathlib

namespace PiIrrationality

theorem mahler_auxiliary_polynomials (n : ℕ) (hn : 50 ≤ n) :
    ∃ A : Fin 11 → Fin 11 → Polynomial ℤ,
      (∀ h k, (A h k).natDegree ≤ n)
        ∧ Matrix.det (fun h k : Fin 11 => A h k) ≠ 0
        ∧ (∀ h k (x : ℂ),
            ‖Polynomial.eval x ((A h k).map (Int.castRingHom ℂ))‖
              ≤ (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ ((10 : ℝ) - 3 * (n : ℝ) / 2)
                * ((n : ℝ) + 1) ^ (21 : ℕ) * (Real.sqrt 32) ^ (11 * n)
                * Finset.sum (Finset.range (n + 1)) (fun j => ‖x‖ ^ j))
        ∧ (∀ h (x : ℂ), x ≠ 0 → x ≠ 1 → ‖Complex.log x‖ < (11 : ℝ) / 2 →
            ‖Finset.sum Finset.univ (fun k : Fin 11 =>
              Polynomial.eval x ((A h k).map (Int.castRingHom ℂ))
                * Complex.log x ^ (k : ℕ))‖
              ≤ (Nat.factorial 10 : ℝ) * (2 : ℝ) ^ (-3 * (n : ℝ) / 2)
                * (Real.exp 1 * Real.sqrt (n : ℝ)) ^ (11 : ℕ)
                * Real.exp ((2 * (n : ℝ) + 1) * ‖Complex.log x‖)
                * (‖x‖ / (11 : ℝ)) ^ n) := by
  sorry

end PiIrrationality
