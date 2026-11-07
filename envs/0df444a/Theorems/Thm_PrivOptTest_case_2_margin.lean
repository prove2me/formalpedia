-- Prove2me | Theorems.Thm_PrivOptTest_case_2_margin
-- name    : PrivOptTest.case_2_margin
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:56.129689+00:00
-- url     : https://prove2.me/theorems/78976245-753e-47b6-88d5-efa9bac1b5e3
-- title:
--   Proof of Theorem 3.12, Step 2, Case 2, pp.23–24 — margin 19α/20 in the cumulative-escape case
-- statement:
--   Let $A,B$ be blocks of $k$ records in $\{0,1\}^b$, $H\le b$, $\alpha>0$, $k\ge4\alpha$ and $19\alpha/20\le F(H)<33\alpha/20$. Under the Match order the unnoised statistics of lines 17–18 of Algorithm 2 satisfy
--   $$V_A-V_B\ge\frac{19\alpha}{20},$$
--   and under the Far order $V_A-V_B\le-19\alpha/20$.
--
--   Together with the Laplace tail this decides the output in the cumulative-escape case.
--
--   Differences from the source:
--   - reading: "Suppose Δ̂ < α/2. Under B^c_bs …" → the hypotheses 19α/20 ≤ F(H) < 33α/20, k ≥ 4α, α > 0; reason: these are the facts the paragraph derives and uses (p.23)
--   - encoding: Match and Far promises → MatchOrder and FarOrder on the blocks; reason: Lemma 3.5 and Remark 3.6
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2-Case 2, pp.23–24

import Mathlib
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Proof of Theorem 3.12, Step 2, Case 2** (cumulative escape, pp.23–24). Let the blocks have size
`n`, `H ≤ b`, `α > 0`, `n ≥ 4α` and `19α/20 ≤ F(H) < 33α/20`. Under the Match promise the difference
between Alice's and Bob's unnoised statistics of lines 17–18 of Algorithm 2 is at least `19α/20`; under the
Far promise it is at most `−19α/20`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2-Case 2, pp.23–24.

**Formalization Note.** The statistic is `statCum b H` on each party's own records, maxima over all of
`{0,1}^H`. `q < p` is the integer (lexicographic) order of nodes. -/
theorem case_2_margin (b k H : ℕ) (α : ℝ) (A B : List ℕ) (hAl : A.length = k) (hBl : B.length = k)
    (hA : ∀ x ∈ A, x < 2 ^ b) (hB : ∀ x ∈ B, x < 2 ^ b) (hH : H ≤ b) (hα : 0 < α)
    (hk : 4 * α ≤ k) (hF1 : 19 * α / 20 ≤ (escaped k b H A B : ℝ))
    (hF2 : (escaped k b H A B : ℝ) < 33 * α / 20) :
    (MatchOrder A B → 19 * α / 20 ≤ ((statCum b H A - statCum b H B : ℤ) : ℝ)) ∧
      (FarOrder A B → ((statCum b H A - statCum b H B : ℤ) : ℝ) ≤ -(19 * α / 20)) := by sorry

end PrivOptTest
