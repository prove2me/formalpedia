-- Prove2me | Theorems.Thm_ReplParity_card_subspaces_le
-- name    : ReplParity.card_subspaces_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:41.900225+00:00
-- url     : https://prove2.me/theorems/c21efb16-5955-4030-897c-5bdb98e7cfb9
-- title:
--   §2.1, p.11 — $\mathbb F_2^n$ has at most $2^{n^2}$ subspaces, each with an $n^2$-bit encoding
-- statement:
--   For every $n$, the space $\mathbb F_2^n$ has at most $2^{n^2}$ subspaces, and there is an injective encoding of subspaces by $n\times n$ matrices over $\mathbb F_2$, i.e. by $n^2$ bits.
--
--   The count is the union bound over subspaces in the coverage arguments of Lemma 3.2 and Proposition 3.5.
--
--   Differences from the source:
--   - encoding: a canonical encoding of O(n²) bits (reduced row echelon bases) → some injective map from subspaces to n × n matrices over 𝔽₂; reason: an n × n matrix is n² bits, the O(n²) bound with constant 1; the RREF basis padded with zero rows is one such map
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- **Counting and encoding subspaces of 𝔽ⁿ₂.** Shen, Zhong, *Replicable Parity Learning: Cubic
Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), §2.1, p.11 (PDF p.13): "Subspaces of 𝔽ⁿ₂ are represented by their reduced row echelon
bases, so 𝔽ⁿ₂ has at most 2^{n²} subspaces and each has a canonical encoding of O(n²) bits."

𝔽ⁿ₂ has at most `2^{n²}` subspaces, and subspaces are encoded injectively by `n × n` matrices over
𝔽₂ (`n²` bits). -/
theorem card_subspaces_le (n : ℕ) :
    Nat.card (Subsp n) ≤ 2 ^ (n ^ 2) ∧
    ∃ f : Subsp n → (Fin n → Fin n → ZMod 2), Function.Injective f := by sorry

end ReplParity
