-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_padding
-- name    : SyncPrefix.Huffman.padding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:57.039992+00:00
-- url     : https://prove2.me/theorems/f93119a2-4e77-4e6b-9f2c-260046481a64
-- title:
--   Proof of Corollary 8, p. 8 — the Set Cover hardness persists on instances whose minimum cover has size at least d log |X|
-- statement:
--   Assume the Set Cover hardness of [4]: for every $\gamma > 0$ there is $c' > 0$ such that a polynomial-time $c' \log p$-approximation of Set Cover on instances with $|C| \le |X|^{1+\gamma}$, $p = |X|$, implies P = NP.
--
--   Then for every $\gamma > 0$ and every $d > 0$ there is $c' > 0$ such that the following holds: if some polynomial-time algorithm approximates Set Cover within $c' \log p$ on all instances with
--   $$|C| \le |X|^{1+\gamma} \quad\text{and}\quad \mathrm{OPT}(X, C) \ge d \log |X|$$
--   (for $p = |X|$ large enough), then P = NP.
--
--   In the proof of Corollary 8 this lets the additive $\Theta((\log k)^2)$ term of the composition be absorbed into the multiplicative factor. The paper justifies the claim by enumerating all subfamilies of size at most $d \log |X|$, which takes about $|C|^{d \log |X|}$ steps and is not polynomial; the claim itself is the statement above.
--
--   Differences from the source:
--   - generalization: "for some d > 0" → for every d > 0; reason: Corollary 8 needs d of order (1 + γ)/ln 2, and the statement for every d implies it for some d.
--   - reading: the hardness of [4] → a hypothesis (`SetCoverHardness`), in value form with a threshold n₀; reason: a cited theorem the paper does not prove.
--   - encoding: log |X| → the natural logarithm of p; reason: the base is absorbed in d and c′.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (third paragraph)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Complexity

namespace SyncPrefix.Huffman

/-- The padding claim (p. 8), under the Set Cover hardness of [4]: for every `γ > 0` and every
`d > 0` there is `c' > 0` such that a polynomial-time `c' log p`-approximation of Set Cover on
instances with `|C| ≤ p^{1+γ}` whose minimum cover has size at least `d log p` implies `P = NP`. -/
theorem padding (hSC : SetCoverHardness) :
    ∀ γ : ℝ, 0 < γ → ∀ d : ℝ, 0 < d → ∃ c' : ℝ, 0 < c' ∧
      (SCApproxWithinOn
        (fun I => (I.sets.length : ℝ) ≤ (I.n : ℝ) ^ (1 + γ) ∧ d * Real.log I.n ≤ minCover I)
        (fun p => c' * Real.log p) → PEqNP) := by sorry

end SyncPrefix.Huffman
