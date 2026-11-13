-- Prove2me | Theorems.Thm_SaglamGV_circuit_sum_rank
-- name    : SaglamGV.circuit_sum_rank
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:10.958423+00:00
-- url     : https://prove2.me/theorems/ba8db834-1fb8-47c1-9f3a-3786f6be2960
-- title:
--   Circuits in $B_d$ sum to zero, have rank $\ell-1$, and $3\le\ell\le n+1$
-- statement:
--   Let $S\subseteq B_d$ be a circuit (an inclusion-minimal linearly dependent subset) with $|S|=\ell$. Then
--
--   $$
--   \sum_{x\in S}x=0,\qquad \operatorname{rank}(S)=\ell-1,\qquad 3\le\ell\le n+1 .
--   $$
--
--   These facts feed the first-moment computation: a circuit with $\ell$ elements lies in $\ker M$ with probability $2^{-m(\ell-1)}$, and only sizes $3\le\ell\le n+1$ occur.
--
--   Differences from the source:
--   - generalization: the identity inside the standing regime ln n ≪ w ≤ (1/2 − ε)n of §2 → every n and d; reason: the statement is an exact combinatorial/probabilistic identity or bound that does not use the regime; it specializes to the paper's case
--   - encoding: rank(S) → Module.finrank of the 𝔽₂-span of S; reason: the rank of a set of vectors is the dimension of its span
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.2 (display Σ_{x∈S} x = 0, rank(S) = ℓ − 1, 3 ≤ ℓ ≤ n + 1)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Circuit

namespace SaglamGV

/-- Structure of circuits in $B_d$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.2: "If C_ℓ is the collection of ℓ-element circuits
in B_d, then every S ∈ C_ℓ satisfies Σ_{x∈S} x = 0, rank(S) = ℓ − 1, where 3 ≤ ℓ ≤ n + 1").

Every $ℓ$-element circuit $S ⊆ B_d$ sums to zero, spans a subspace of dimension $ℓ − 1$, and has
$3 ≤ ℓ ≤ n + 1$.

**Formalization Note** `rank(S)` is the dimension of the $𝔽_2$-span of $S$. -/
theorem circuit_sum_rank (n d ℓ : ℕ) (S : Finset (Fin n → ZMod 2)) (hS : S ∈ circuits n d ℓ) :
    ∑ x ∈ S, x = 0 ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set (Fin n → ZMod 2))) = ℓ - 1 ∧
      3 ≤ ℓ ∧ ℓ ≤ n + 1 := by sorry

end SaglamGV
