-- Prove2me | Theorems.Thm_SelfSelReg_proposition_G_1_exponents
-- name    : SelfSelReg.proposition_G_1_exponents
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:54.823202+00:00
-- url     : https://prove2.me/theorems/5f893c54-90b6-4744-b51e-fc685e83f97e
-- title:
--   Proposition G.1 (proof), (184) and (186) — exponent comparisons for the total sample count
-- statement:
--   Let $2\le k\le n$, $\varepsilon\in(0,1)$, $B\ge1$, $\Delta\in(0,1]$, and let $K$, $s$ and $\varepsilon_{\mathrm{int}}$ be the hyperparameters of Hyperparameters 4.1. Then
--   $$\log\frac{nk}{\varepsilon_{\mathrm{int}}}=\log(nk)+\max\Big\{\log\frac1\varepsilon,K^6s\Big\}\le(1+2K^{10})\log\frac{nk}{\varepsilon}\le3K^{10}\log\frac{nk}{\varepsilon},\tag{184}$$
--   and
--   $$k\Big[(nk)^{4K^{10}+12K^4}+\Big(\frac{nk}{\varepsilon}\Big)^{15K^{12}}\Big]\le2\Big(\frac{nk}{\varepsilon}\Big)^{15K^{12}+1}\le2\Big(\frac{nk}{\varepsilon}\Big)^{K^{13}}.\tag{186}$$
--
--   These are the two computations that turn the per-call sample bounds of Theorems 6.1 and 7.1 into the total sample bound $\widetilde O((nk/\varepsilon)^{K^{13}}\log(1/\delta))$ of the recovery algorithm.
--
--   **Formalization Note** Every step of both chains is stated. The facts $K\ge128$ (181), $s\le 2K^4\log n$ (182) and (183) used on the page follow from the hyperparameter choices. Real powers, natural logarithm.
--
--   Differences from the source:
--   - reading: s := K⁴ log n (9), printed as a real number → s = ⌈K⁴ log n⌉ (hypS), natural logarithm; reason: s is used as a tensor order ("let s ≥ 1 be an integer", Lemmas 5.7, 5.8) and (182) states s ≤ 2K⁴ log n, which presupposes rounding up; the ceiling is also the stronger choice for every bound that improves with s
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), proof of Proposition G.1, (181)–(186), pp.94–95 (PDF pp.97–98)

import Mathlib
import Definitions.Def_SelfSelReg_hypK

namespace SelfSelReg

/-- **Proposition G.1** (Complexity of Full Recovery), proof: the exponent comparisons (184) and (186).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), proof of Proposition G.1, p.95 (PDF p.98), using (181)–(183) of p.94:
"log(nk/ε_int) = log(nk) + max{log(1/ε), K⁶s} (choice of ε_int (183)) ≤ (1 + 2K¹⁰) log(nk/ε) (choice of
s (182)) ≤ 3K¹⁰ log(nk/ε)." (184) "Since k ≤ nk/ε and 4K¹⁰ + 12K⁴ ≤ 15K¹², we have
k[(nk)^{4K¹⁰+12K⁴} + (nk/ε)^{15K¹²}] ≤ 2(nk/ε)^{15K¹²+1} ≤ 2(nk/ε)^{K¹³}." (186)

**Formalization Note.** `K = hypK B ∆`, `s = hypS B ∆ n = ⌈K⁴ log n⌉`, `ε_int = hypEpsInt B ∆ ε n`
(Hyperparameters 4.1), for `2 ≤ k ≤ n`, `ε ∈ (0, 1)` and the constants `B ≥ 1`, `∆ ∈ (0, 1]` of
Assumption 1.2; the facts (181) `K ≥ 128`, (182) `s ≤ 2K⁴ log n` and (183) are consequences of these
choices. Each step of both chains is stated. Powers are real powers; natural logarithm. The failure
probability `δ` of Proposition G.1 does not enter these two displays. -/
theorem proposition_G_1_exponents (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ ε : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hε : 0 < ε) (hε1 : ε < 1) (K εint : ℝ) (s : ℕ)
    (hKdef : K = hypK B Δ) (hsdef : s = hypS B Δ n) (hεdef : εint = hypEpsInt B Δ ε n) :
    -- (184)
    (Real.log ((n : ℝ) * k / εint) = Real.log ((n : ℝ) * k) + max (Real.log (1 / ε)) (K ^ 6 * s) ∧
      Real.log ((n : ℝ) * k) + max (Real.log (1 / ε)) (K ^ 6 * s) ≤
        (1 + 2 * K ^ 10) * Real.log ((n : ℝ) * k / ε) ∧
      (1 + 2 * K ^ 10) * Real.log ((n : ℝ) * k / ε) ≤ 3 * K ^ 10 * Real.log ((n : ℝ) * k / ε)) ∧
    -- (186)
    ((k : ℝ) * (((n : ℝ) * k) ^ (4 * K ^ 10 + 12 * K ^ 4) + ((n : ℝ) * k / ε) ^ (15 * K ^ 12)) ≤
        2 * ((n : ℝ) * k / ε) ^ (15 * K ^ 12 + 1) ∧
      2 * ((n : ℝ) * k / ε) ^ (15 * K ^ 12 + 1) ≤ 2 * ((n : ℝ) * k / ε) ^ (K ^ 13)) := by sorry

end SelfSelReg
