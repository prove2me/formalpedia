-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_affine_hash_survival
-- name    : SubsetSumPartialMatch.SubsetSum.affine_hash_survival
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:23.872578+00:00
-- url     : https://prove2.me/theorems/f7bdd6f1-8e36-4566-81aa-a088b39a42bb
-- title:
--   Lemma 2.3 — power-of-two affine hashing
-- statement:
--   Let $q\le p$ be powers of two and let $h$ be uniform in $H_p$.
--
--   1. For every $k\in\mathbb Z$, $\Pr[h(k)\in I_q]=q/p$.
--   2. For all $k_1,k_2\in\mathbb Z$ with $0<|k_1-k_2|<q$, the events $h(k_1)\in I_q$ and $h(k_2)\in I_q$ are independent.
--
--   This family replaces hashing modulo a random prime, which would cause technical trouble for integers of $2^{o(n)}$ bits.
--
--   Differences from the source:
--   - encoding: $q\le p$ powers of two → $p=2^u$, $q=2^v$ with $v\le u$; reason: the same pairs
--   - encoding: the events are independent → the probability of the intersection is the product of the probabilities; reason: the definition of independence of two events
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 11, Lemma 2.3

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Hash

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.3. Let `q ≤ p` be powers of two and `h` uniform in `H_p`. Every integer survives with
probability `q/p`, and two integers at distance in `(0, q)` survive independently. -/
theorem affine_hash_survival (u v : ℕ) (hvu : v ≤ u) :
    (∀ k : ℤ, hashProb (2 ^ u) (fun α β => Survives (2 ^ u) (2 ^ v) α β k) =
      ((2 : ℝ) ^ v) / (2 : ℝ) ^ u) ∧
    (∀ k₁ k₂ : ℤ, 0 < |k₁ - k₂| → |k₁ - k₂| < 2 ^ v →
      hashProb (2 ^ u) (fun α β => Survives (2 ^ u) (2 ^ v) α β k₁ ∧
          Survives (2 ^ u) (2 ^ v) α β k₂) =
        hashProb (2 ^ u) (fun α β => Survives (2 ^ u) (2 ^ v) α β k₁) *
          hashProb (2 ^ u) (fun α β => Survives (2 ^ u) (2 ^ v) α β k₂)) := by sorry

end SubsetSumPartialMatch.SubsetSum
