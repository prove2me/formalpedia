-- Prove2me | Theorems.Thm_PermutationStreams_Parity_block_inversions
-- name    : PermutationStreams.Parity.block_inversions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:19.53226+00:00
-- url     : https://prove2.me/theorems/673c079d-f3a6-4c10-b1af-28fbfc1fdcc1
-- title:
--   Lemma 4.5 — inversion count and sign of the block permutation
-- statement:
--   Let $x,y,z\in[3]^m$ be a promised input (every $(x_i,y_i,z_i)$ is a permutation of $[3]$) and let $\pi=A(x)B(y)C(z)$ be the block permutation of $[3m]$. Then
--
--   $$
--   \operatorname{inv}(\pi)=3\binom m2+\sum_{i=1}^m\operatorname{inv}(x_i,y_i,z_i),
--   $$
--
--   and consequently
--
--   $$
--   \operatorname{sgn}(\pi)=(-1)^{3\binom m2}\,f_m(x,y,z).
--   $$
--
--   The second identity is the reduction step: a streaming algorithm for the sign, run block by block by the three players, computes $f_m$ up to a correction depending only on $m$.
--
--   **Formalization Note** $\pi$ is the sequence of block values in the $0$-based encoding (each value one less than the paper's), and $\operatorname{sgn}(\pi)=(-1)^{\operatorname{inv}(\pi)}$; both identities are stated.
--
--   Differences from the source:
--   - encoding: π ∈ S_{3m} with values 3(i−1)+w_i → the sequence k ↦ 3i + w_i (0-based) in ℕ, with sgn = (−1)^inv; reason: an order-preserving shift by one; the sign of a permutation is defined from its inversions
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.3, p. 8, Lemma 4.5 (construction on p. 7)

import Definitions.Def_PermutationStreams_Parity_SignProblem

namespace PermutationStreams.Parity

/-- Braverman–Zamir, Lemma 4.5, p.8. For a promised input `(x, y, z)`, the concatenation
`π = A(x) B(y) C(z)` satisfies `inv(π) = 3·C(m,2) + ∑ᵢ inv(xᵢ, yᵢ, zᵢ)` and consequently
`sgn(π) = (-1)^{3·C(m,2)} f_m(x, y, z)`. -/
theorem block_inversions (m : ℕ) (x y z : Fin m → Fin 3) (h : Promised m x y z) :
    inv (blockStream m x y z) = 3 * m.choose 2 + ∑ i, inv (tripleSeq (x i, y i, z i)) ∧
    sgnSeq (blockStream m x y z) = (-1) ^ (3 * m.choose 2) * fm m x y z := by sorry

end PermutationStreams.Parity
