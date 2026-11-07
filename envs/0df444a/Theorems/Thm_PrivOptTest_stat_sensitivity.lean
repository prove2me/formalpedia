-- Prove2me | Theorems.Thm_PrivOptTest_stat_sensitivity
-- name    : PrivOptTest.stat_sensitivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:52.46224+00:00
-- url     : https://prove2.me/theorems/0783f967-e4c9-4de7-bd09-d73bbbac6cbc
-- title:
--   Proof of Theorem 3.12, pp.23–24 — sensitivity 7 per maximization, 14 per statistic
-- statement:
--   If two lists of records differ by one replacement, then each of the four maximizations of lines 14–18 of Algorithm 2 changes by at most $7$, and each of the two statistics (a difference of two maximizations) by at most $14$, for every $L$ and $H$.
--
--   With privacy budget $\varepsilon/2$ this justifies the noise $\mathrm{Lap}(28/\varepsilon)$ of the final releases.
--
--   Differences from the source:
--   - generalization: "changing one record" of a block → any two lists differing by one replacement, any depths L, H; reason: specializes to the source: blocks of neighbouring datasets differ by one replacement (Remark 3.6)
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2, p.23 (Case 1) and p.24 (Case 2)

import Mathlib
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Sensitivity of the final statistics** (proof of Theorem 3.12, pp.23–24). If two record lists
differ by one replacement, each maximization of lines 14–18 of Algorithm 2 changes by at most `7`, and
each difference of two maximizations by at most `14`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2, p.23 (Case 1) and p.24 (Case 2).

**Formalization Note.** No promise and no relation between `L`, `H` and `b` is needed. Blocks of
neighbouring datasets differ by one replacement by Remark 3.6 (`remark_3_6_blocks`). -/
theorem stat_sensitivity (b L H : ℕ) (l l' : List ℕ) (h : OneReplaced l l') :
    (∀ j < 2, |(jumpMax b L j l : ℤ) - jumpMax b L j l'| ≤ 7) ∧
      |(cumLeftMax b H l : ℤ) - cumLeftMax b H l'| ≤ 7 ∧
      |(cumRightMax b H l : ℤ) - cumRightMax b H l'| ≤ 7 ∧
      |statJump b L l - statJump b L l'| ≤ 14 ∧
      |statCum b H l - statCum b H l'| ≤ 14 := by sorry

end PrivOptTest
