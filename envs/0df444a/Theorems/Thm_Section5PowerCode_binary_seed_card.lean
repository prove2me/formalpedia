-- Prove2me | Theorems.Thm_Section5PowerCode_binary_seed_card
-- name    : Section5PowerCode.binary_seed_card
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:06:03.198127+00:00
-- url     : https://prove2.me/theorems/cf4cbd50-cb10-5711-a7f2-f7de58c9c276
-- title:
--   Number of seeds in a binary power code
-- statement:
--   Let $r,k\in\mathbb N$ with $r
--   e0$. The seed space of length $k$ over the field with $2^r$ elements has cardinality
--
--   $$|(\mathbb F_{2^r})^k|=2^{rk}.$$
--
--   This gives the exact randomness-space size, including $k=0$.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5BinaryPowerCode.lean, lines 15–17.

import Definitions.Def_Section5Verified_Section5BinaryPowerCode
import Mathlib
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode

theorem Section5PowerCode.binary_seed_card {r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    Fintype.card (Fin k → GaloisField 2 r)=2^(r*k) := by sorry
