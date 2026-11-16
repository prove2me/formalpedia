-- Prove2me | Theorems.Thm_PrivOptTest_Supplement_theorem_4_9
-- name    : PrivOptTest.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:37:18.031656+00:00
-- url     : https://prove2.me/theorems/1ede8e8a-505e-4fc6-bb10-0808c3c0856d
-- title:
--   Theorem 4.9, p.33 — a non-interactive $\varepsilon$-private halfspace tester at resolution $t=n$ for $n\ge C/\varepsilon^2$
-- statement:
--   There are a universal constant $C>0$ and a constant $k$ (line 1 of Algorithm 4) such that the following holds. Let $\mathcal X\subseteq\mathbb R^d\setminus\{0\}$ be finite, $\varepsilon>0$ and $n\ge C/\varepsilon^2$. Then Algorithm 4 with this $k$ is non-interactive, and it is an $\varepsilon$-private tester for $\mathcal H_{\mathrm{hs}}$ with resolution
--   $$t=n$$
--   and success probability $0.9$ (Definition 1.2).
--
--   Resolution $n$ is the largest one can ask for, since the classifier $w=0$ makes exactly $n$ mistakes; the theorem covers the small-data regime, where Theorem 4.7 needs far more data.
--
--   Differences from the source:
--   - reading: “Let k be a large enough constant” → ∃ k : ℕ, chosen with C and independent of d, X, ε, n; reason: k is a constant of the algorithm; a large enough one exists
--   - encoding: non-interactive → IsNonInteractive: Alice speaks at round 0, Bob's round-1 message ignores hers, the run stops at round 2 with an output computed from the public coins and the two messages; reason: each party sends one message from its own data, private coins and public coins, and the output is a function of the releases (pp.33–34, 51–53)
--   - encoding: the set ℛ of rays meeting X → rays recorded by the points of X on them; reason: for X ⊆ ℝ^d \ {0} the classes partition X and give the same counts a_R
--   - encoding: testers on multisets → IsTester … over protocols on sequences Fin n → X; reason: Algorithm 4 reads its input only through the ray counts a_R, b_R, which do not depend on the order of the records, and sequence neighbours are multiset neighbours
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 4.9, p.33; Algorithm 4, p.33; proof pp.51–52

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Supplement_HhsOn
import Definitions.Def_PrivOptTest_Supplement_IsNonInteractive
import Definitions.Def_PrivOptTest_Supplement_algo4

namespace PrivOptTest

namespace Supplement

/-- **Theorem 4.9** (arXiv:2611.03599, manuscript sha256 4ac94dcf…, p.33; Algorithm 4, p.33). There are
a universal constant `C > 0` and a constant `k` (line 1 of Algorithm 4) such that for every finite
`X ⊆ ℝ^d \ {0}`, every `ε > 0` and every `n ≥ C/ε²`, Algorithm 4 is non-interactive and is an ε-private
tester (Definition 1.2, success probability 0.9) for `H_hs` with resolution `t = n`.

**Formalization Note.** "Let `k` be a large enough constant": `k` is existential and depends on
nothing, like `C`. Algorithm 4 is the protocol `algo4 X n k ε`: public random signs, private
`Lap(2k/ε)` noise, `τ = √n/2`, Match on a strict exceedance. -/
theorem theorem_4_9 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (d : ℕ) (X : Finset (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (n : ℕ),
      (0 : EuclideanSpace ℝ (Fin d)) ∉ X → 0 < ε → C / ε ^ 2 ≤ n →
      IsNonInteractive (algo4 X n k ε) ∧ IsTester (algo4 X n k ε) (HhsOn X) ε n (1 / 10) := by sorry

end Supplement

end PrivOptTest
