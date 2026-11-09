-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_theorem_1_2_steps
-- name    : PolyEvalDS.LargeChar.theorem_1_2_steps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:37.176789+00:00
-- url     : https://prove2.me/theorems/4342ce08-784c-4885-8065-7524987017f9
-- title:
--   Proof of Theorem 1.2, recursion bound (p. 10) — $B_{i+1}=2\sqrt{dB_i}$ reaches $(4+4\varepsilon)d$ within $\lceil\tilde k\rceil$ steps
-- statement:
--   Let $B_0=d^{60}$ and $B_{i+1}=2\sqrt{dB_i}$, and let
--   $$\tilde k=\log_2\ln d-\log_2(\varepsilon/2)+\log_260.$$
--   For every integer $d\ge2$ and every real $\varepsilon$ with $0<\varepsilon\le\frac12$ there is an index $k\le\lceil\tilde k\rceil$ with
--   $$B_k\le(4+4\varepsilon)d.$$
--
--   This bounds the number of applications of Proposition 3.1 in the proof of Theorem 1.2, and hence the factor $(d+1)^{\lceil\tilde k\rceil}$ that accounts for the terms $\log_2\ln d-\log_2\varepsilon$ in the exponent of the goal.
--
--   Differences from the source:
--   - generalization: the proof is under "for sufficiently large d" → every d ≥ 2; reason: the bound already holds there; large d is a special case
--   - encoding: let k be the smallest index with B_k ≤ (4+4ε)d, so we have to show k ≤ ⌈k̃⌉ → there is k ≤ ⌈k̃⌉₊ with B_k ≤ (4+4ε)d, the ceiling truncated at 0; reason: some index below the bound holds exactly when the smallest one does; k̃ > 0 here, so the truncation changes nothing
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, proof of Theorem 1.2, p. 10

import Mathlib
import Definitions.Def_PolyEvalDS_LargeChar_Recursions

namespace PolyEvalDS.LargeChar

/-- Proof of Theorem 1.2, p. 10: `B₀ = d⁶⁰`, `B_{i+1} = 2√(d B_i)` reaches `(4+4ε)d` within `⌈k̃⌉`
steps, with `k̃ = log₂ ln d − log₂(ε/2) + log₂ 60`. -/
theorem theorem_1_2_steps :
    ∀ (d : ℕ) (ε : ℝ), 2 ≤ d → 0 < ε → ε ≤ 1 / 2 →
      ∃ k : ℕ,
        k ≤ ⌈Real.logb 2 (Real.log d) - Real.logb 2 (ε / 2) + Real.logb 2 60⌉₊ ∧
          lineSeq d k ≤ (4 + 4 * ε) * (d : ℝ) := by sorry

end PolyEvalDS.LargeChar
