-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_sec_B_9_4
-- name    : RandOrderKnapGAP.Integral.sec_B_9_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:27:05.607439+00:00
-- url     : https://prove2.me/theorems/ac9cc1be-328e-49ec-aaca-376144ea7399
-- title:
--   §B.9.4 — $\gamma^*-A/10^{10}-10^{-8}=0.256448039\ldots>0.2564$ with the exact rationals
-- statement:
--   With $N=\max\{n,10^{10}\}$ and $\varepsilon_{\mathrm{samp}}\le10^{-8}$,
--   $$\gamma^*-\frac AN-\varepsilon_{\mathrm{samp}}\ \ge\ \gamma^*-\frac A{10^{10}}-10^{-8}=0.25644803923547484138\ldots>0.2564 ,$$
--   where $\gamma^*$ and $A$ are the exact rationals (B.48) and (B.54).
--
--   This is the arithmetic that turns the finite-horizon coefficient into the constant $0.2564$ of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: ε_samp ∈ [0, 10⁻⁸] (a probability) → any real ε ≤ 10⁻⁸; reason: the inequality needs only the upper bound; probabilities are an instance
--   - encoding: = 0.25644803923547484138 … → 0.25644803923547484138 ≤ value < 0.25644803923547484139; reason: the printed digits as a two-sided bound
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 60 (PDF 62), §B.9.4

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Constants

namespace RandOrderKnapGAP.Integral

/-- **§B.9.4**, p. 60. With `N = max{n, 10¹⁰}` and `ε_samp ≤ 10⁻⁸`,
`γ* − A/N − ε_samp ≥ γ* − A/10¹⁰ − 10⁻⁸ = 0.25644803923547484138… > 0.2564`, where `γ*` and
`A` are the exact rationals (B.48) and (B.54). -/
theorem sec_B_9_4 :
    (∀ (n : ℕ) (ε : ℝ), ε ≤ 1 / 10 ^ 8 →
      (gammaStar : ℝ) - (Aconst : ℝ) / 10 ^ 10 - 1 / 10 ^ 8
        ≤ (gammaStar : ℝ) - (Aconst : ℝ) / ((max n (10 ^ 10) : ℕ) : ℝ) - ε) ∧
    (0.25644803923547484138 : ℝ) ≤ (gammaStar : ℝ) - (Aconst : ℝ) / 10 ^ 10 - 1 / 10 ^ 8 ∧
    (gammaStar : ℝ) - (Aconst : ℝ) / 10 ^ 10 - 1 / 10 ^ 8 < (0.25644803923547484139 : ℝ) ∧
    (0.2564 : ℝ) < (gammaStar : ℝ) - (Aconst : ℝ) / 10 ^ 10 - 1 / 10 ^ 8 := by sorry

end RandOrderKnapGAP.Integral
