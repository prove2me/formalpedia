-- Prove2me | Theorems.Thm_QWildMatch_block_partition
-- name    : QWildMatch.block_partition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:13.556067+00:00
-- url     : https://prove2.me/theorems/fe849ae4-d8a6-494b-bfc3-5569c63615e5
-- title:
--   §6.1 — the blocks partition the starts, and $|J_b|\le L+\ell$
-- statement:
--   Let $L\ge1$. The number of blocks is $N_B=\lceil(n+1)/L\rceil$, every start $0\le s\le n$ lies in exactly one block $I_b$ with $b<N_B$, every block has at most $L$ starts, and
--
--   $$|J_b|\le L+\ell.$$
--
--   These counts turn the per-block cost of the list circuit into the bound (2) of Theorem 6.5.
--
--   Differences from the source:
--   - reading: partition the starts into consecutive blocks of at most $L$ starts → the partition $bL\le s<(b+1)L$; reason: the page does not name a partition, and this is the canonical one with $\lceil(n+1)/L\rceil$ blocks.
--   - generalization: $\ell=m+r_+$ → any natural number $\ell$; reason: the page's $\ell$ is an instance and the count does not use its form.
--   - encoding: $L$ a block length → the hypothesis $L\ge1$; reason: $\lceil(n+1)/L\rceil$ is undefined at $L=0$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §6.1, p.8

import Mathlib
import Definitions.Def_QWildMatch_J

namespace QWildMatch

/-- The block facts of §6.1, Zhao et al., STOC 2027 submission (file sha256 9e87a9dd…), p.8: there are
`N_B = ⌈(n + 1)/L⌉` blocks, each of the `n + 1` starts lies in exactly one block, each block has at most
`L` starts, and `|J_b| ≤ L + ℓ`.

**Formalization Note** `ℓ` is an arbitrary natural number here; the page's `ℓ = m + r₊` is one
instance. `|J_b| ≤ L + ℓ` holds for every `b`, and for `b ≥ N_B` the block is empty. -/
theorem block_partition (n L l : ℕ) (hL : 1 ≤ L) :
    NB n L = ⌈((n : ℝ) + 1) / (L : ℝ)⌉₊ ∧
    (∀ s : ℕ, s ≤ n → ∃! b : ℕ, b < NB n L ∧ s ∈ I n L b) ∧
    (∀ b : ℕ, (I n L b).card ≤ L) ∧
    (∀ b : ℕ, (J n L l b).card ≤ L + l) := by sorry

end QWildMatch
