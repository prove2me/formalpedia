-- Prove2me | Theorems.Thm_PrivOptTest_case_1_margin
-- name    : PrivOptTest.case_1_margin
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:48.133954+00:00
-- url     : https://prove2.me/theorems/c40a3b09-3c9d-4e4b-a728-e60f05aa8f35
-- title:
--   Proof of Theorem 3.12, Step 2, Case 1, pp.22–23 — margin 4α/5 in the large-jump case
-- statement:
--   Let $A,B$ be blocks of $k$ records in $\{0,1\}^b$, $L+1\le b$, $H=L+1$, $\alpha>0$, $k\ge4\alpha$, $F(L)\le21\alpha/20$ and $\Delta=F(H)-F(L)\ge2\alpha/5$. If every record of $A$ is below every record of $B$ (Match), then
--   $$V_A-V_B\ge\frac{4\alpha}5,$$
--   where $V_A,V_B$ are the unnoised statistics of lines 14–15 of Algorithm 2 on each party's own records; if every record of $A$ is above every record of $B$ (Far), then $V_A-V_B\le-4\alpha/5$.
--
--   Together with the Laplace tail this decides the output in the large-jump case.
--
--   Differences from the source:
--   - reading: "under B^c_bs … suppose Δ̂ ≥ α/2" → the hypotheses F(L) ≤ 21α/20, Δ ≥ 2α/5, k ≥ 4α, α > 0; reason: these are exactly the facts the paragraph derives and uses (p.22); α > 0 by its definition
--   - encoding: Match and Far promises → MatchOrder and FarOrder on the blocks; reason: Lemma 3.5 and Remark 3.6
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2-Case 1, pp.22–23

import Mathlib
import Definitions.Def_PrivOptTest_Trie

namespace PrivOptTest

/-- **Proof of Theorem 3.12, Step 2, Case 1** (large jump, pp.22–23). Let the blocks have size `n`,
let `H = L + 1 ≤ b`, `α > 0`, `n ≥ 4α`, `F(L) ≤ 21α/20` and `Δ = F(H) − F(L) ≥ 2α/5`. Under the Match
promise the difference between Alice's and Bob's unnoised statistics of lines 14–15 of Algorithm 2 is at
least `4α/5`; under the Far promise it is at most `−4α/5`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 2-Case 1, pp.22–23.

**Formalization Note.** The statistic is `statJump b L` on each party's own records, with the maxima
over all of `{0,1}^L`, as Algorithm 2 computes it (not over the common node, which is the proof's
conclusion). Match and Far promises are `MatchOrder` and `FarOrder` on the blocks. -/
theorem case_1_margin (b k L : ℕ) (α : ℝ) (A B : List ℕ) (hAl : A.length = k) (hBl : B.length = k)
    (hA : ∀ x ∈ A, x < 2 ^ b) (hB : ∀ x ∈ B, x < 2 ^ b) (hL : L + 1 ≤ b) (hα : 0 < α)
    (hk : 4 * α ≤ k) (hFL : (escaped k b L A B : ℝ) ≤ 21 * α / 20)
    (hΔ : 2 * α / 5 ≤ (escaped k b (L + 1) A B : ℝ) - escaped k b L A B) :
    (MatchOrder A B → 4 * α / 5 ≤ ((statJump b L A - statJump b L B : ℤ) : ℝ)) ∧
      (FarOrder A B → ((statJump b L A - statJump b L B : ℤ) : ℝ) ≤ -(4 * α / 5)) := by sorry

end PrivOptTest
