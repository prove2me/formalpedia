-- Prove2me | Theorems.Thm_QuadStatRE_Main_fact_6_1
-- name    : QuadStatRE.Main.fact_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:57.599101+00:00
-- url     : https://prove2.me/theorems/7d13373b-82d5-480f-be5e-3d23b68fff74
-- title:
--   Fact 6.1 — the counting polynomial: closed form (6.3), weight enumerator of D, P = 1 + 245z³ + 735z⁴ + ⋯, exact P(1/16)
-- statement:
--   Let $P(z)=\mathbb E_{A\leftarrow\mathbb F_2^{3\times4}}[(1+7z)^{15-w(A)}(1-z)^{w(A)}]$ be the counting polynomial (6.2) and $D=\{\delta\in G^I:\sum_{u\in I}u_i\delta_u=0\ \forall i\in[4]\}$ the code of Remark 6.3. Then
--   $$P(z)=\frac1{4096}\Big[(1+7z)^{15}+105(1+7z)^7(1-z)^8+1470(1+7z)^3(1-z)^{12}+2520(1+7z)(1-z)^{14}\Big]. \tag{6.3}$$
--   Moreover, $P$ is the Hamming weight enumerator $\sum_{\delta\in D}z^{\mathrm{wt}(\delta)}$ of $D$; in particular its coefficients are nonnegative and its constant coefficient is one. $D$ has no nonzero word of weight at most two, so $P(z)-1$ has no terms of degree below three; in fact $P(z)=1+245z^3+735z^4+\cdots$. Finally,
--   $$P(1/16)=\frac{1268428846350729617}{1152921504606846976}<1+\frac{1002}{10^4}. \tag{6.4}$$
--
--   These are the numerical facts behind the cubic contraction (Lemma 6.7) and the scalar steps of §7.
--
--   Differences from the source:
--
--   - encoding: the polynomial P and the weight enumerator of D → elements of ℝ[X]; (6.3) as an equality of polynomials; reason: a polynomial identity over ℝ is the identity of the page
--   - encoding: P(z) − 1 has no terms of degree less than three; P(z) = 1 + 245z³ + 735z⁴ + ⋯ → coefficients 0, 1, 2 of P − 1 vanish; coefficient 3 of P is 245 and coefficient 4 is 735; reason: the displayed leading terms as coefficient equalities
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 29, Fact 6.1, (6.3)–(6.4)

import Mathlib
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE Polynomial

namespace QuadStatRE.Main

/-- Fact 6.1 (The counting polynomial), p. 29: the closed form (6.3); `P` is the Hamming weight
enumerator of `D`, with nonnegative coefficients and constant coefficient one; `D` has no nonzero word
of weight at most two, so `P − 1` has no terms of degree below three, and `P = 1 + 245 z³ + 735 z⁴ + ⋯`;
finally (6.4), the exact value of `P(1/16)` and the bound `P(1/16) < 1 + 1002/10⁴`. -/
theorem fact_6_1 :
    countPoly = C (1 / 4096 : ℝ) *
        ((1 + C 7 * X) ^ 15 + C 105 * (1 + C 7 * X) ^ 7 * (1 - X) ^ 8
          + C 1470 * (1 + C 7 * X) ^ 3 * (1 - X) ^ 12 + C 2520 * (1 + C 7 * X) * (1 - X) ^ 14) ∧
    countPoly = weightEnumD ∧
    (∀ i : ℕ, 0 ≤ countPoly.coeff i) ∧ countPoly.coeff 0 = 1 ∧
    (∀ δ ∈ codeD, δ ≠ 0 → 3 ≤ hammingWt δ) ∧
    (∀ i : ℕ, i < 3 → (countPoly - 1).coeff i = 0) ∧
    countPoly.coeff 3 = 245 ∧ countPoly.coeff 4 = 735 ∧
    countPoly.eval (1 / 16) = 1268428846350729617 / 1152921504606846976 ∧
    countPoly.eval (1 / 16) < 1 + 1002 / 10 ^ 4 := by sorry

end QuadStatRE.Main
