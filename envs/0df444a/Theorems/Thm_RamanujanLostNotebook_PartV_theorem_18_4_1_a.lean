-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_theorem_18_4_1_a
-- name    : RamanujanLostNotebook.PartV.theorem_18_4_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T22:11:08.424692+00:00
-- url     : https://prove2.me/theorems/d90c55a1-9db7-456f-b867-b1d3bcbc29e6
-- title:
--   Hirschhorn–Villarino bounds for theta_n
-- statement:
--   For a positive integer $n$ define $\theta_n$ by $n!=\sqrt\pi\,(n/e)^n\big(8n^3+4n^2+n+\theta_n/30\big)^{1/6}$. Then $1-\frac{11}{8n}+\frac{79}{112n^2}<\theta_n<1-\frac{11}{8n}+\frac{79}{112n^2}+\frac{20}{33n^3}$. Not a claim of Ramanujan's manuscript (Hirschhorn–Villarino).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 18, Theorem 18.4.1, p. 384, eq. (18.4.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch18_ch18GammaH

namespace RamanujanLostNotebook.PartV
theorem theorem_18_4_1_a (n : ℕ) (hn : 1 ≤ n) :
    1 - 11 / (8 * (n : ℝ)) + 79 / (112 * (n : ℝ) ^ 2) < 30 * ch18GammaH (n : ℝ) ∧
      30 * ch18GammaH (n : ℝ)
        < 1 - 11 / (8 * (n : ℝ)) + 79 / (112 * (n : ℝ) ^ 2) + 20 / (33 * (n : ℝ) ^ 3) := by sorry
end RamanujanLostNotebook.PartV
