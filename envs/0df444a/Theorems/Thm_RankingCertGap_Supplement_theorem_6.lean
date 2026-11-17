-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_6
-- name    : RankingCertGap.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:59:18.473354+00:00
-- url     : https://prove2.me/theorems/d1a51a95-c03e-4c01-b9ad-e55964966c80
-- title:
--   Theorem 6 — large online-degree capacity, competitiveness, and gap bounds
-- statement:
--   For every integer $d\ge2$,
--   $$
--   \Gamma(d)-\left(1-\frac1e\right)\ge\frac{1}{3ed(d+2)}.
--   $$
--   For all sufficiently large integers $d$,
--   $$
--   \Gamma(d)-\left(1-\frac1e\right)\le O\!\left(\frac{\log d}{d^2}\right),
--   $$
--   $$
--   \frac1{ed^2}-O(d^{-9/4})\le\gamma(d)-\left(1-\frac1e\right)
--   \le\frac1{2ed}+O(d^{-2}),
--   $$
--   $$
--   \Delta(d)\le\frac1{2ed}+O(d^{-2}).
--   $$
--
--   Thus the certifying capacity and RANKING's competitiveness both approach the unrestricted value, while the certifying gap vanishes.
--
--   **Formalization Note** Each $O$ term has an explicit nonnegative real constant chosen before $d$, and all eventual inequalities share an integer threshold. Hence every implicit constant is absolute.
--
--   Differences from the source:
--   - encoding: $O(\log d/d^2)$, $O(d^{-9/4})$, and $O(d^{-2})$ with absolute constants for sufficiently large integer $d$ → explicit nonnegative constants and one integer threshold quantified before $d$; reason: this is the definition of the displayed asymptotic inequalities
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 6, p.9, eqs. (23)–(25)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects

set_option autoImplicit false

namespace RankingCertGap.Supplement

/-- **Theorem 6 (Large online-degree bound).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Theorem 6, p.9, eqs. (23)–(25). The lower capacity bound holds for every integer
`d ≥ 2`; all remaining estimates hold from one integer threshold onward with absolute constants.

**Formalization Note.** Each printed `O` term is represented by a nonnegative real constant chosen
before the degree `d`; one common threshold is used. Thus the constants are absolute. `Real.log` is
the natural logarithm, and the noninteger power `d^(-9/4)` is `Real.rpow`. -/
theorem theorem_6 :
    (∀ d : ℕ, 2 ≤ d →
      1 / (3 * Real.exp 1 * d * (d + 2)) ≤
        GammaC classF (onDegLE d) - (1 - 1 / Real.exp 1)) ∧
    ∃ C_Gamma C_lower C_upper C_gap : ℝ,
      0 ≤ C_Gamma ∧ 0 ≤ C_lower ∧ 0 ≤ C_upper ∧ 0 ≤ C_gap ∧
      ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
        GammaC classF (onDegLE d) - (1 - 1 / Real.exp 1) ≤
            C_Gamma * Real.log d / (d : ℝ) ^ 2 ∧
        1 / (Real.exp 1 * (d : ℝ) ^ 2) - C_lower * (d : ℝ) ^ (-(9 : ℝ) / 4) ≤
            gammaC (onDegLE d) - (1 - 1 / Real.exp 1) ∧
        gammaC (onDegLE d) - (1 - 1 / Real.exp 1) ≤
            1 / (2 * Real.exp 1 * d) + C_upper / (d : ℝ) ^ 2 ∧
        gapC classF (onDegLE d) ≤
            1 / (2 * Real.exp 1 * d) + C_gap / (d : ℝ) ^ 2 := by sorry

end RankingCertGap.Supplement
