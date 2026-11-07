-- Prove2me | Theorems.Thm_TargetedSamplers_proposition_4_24
-- name    : TargetedSamplers.proposition_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:05:19.568048+00:00
-- url     : https://prove2.me/theorems/135acf57-08cf-480a-bd5a-c32474793495
-- title:
--   Proposition 4.24 — the auxiliary layers form a bitonic sorter
-- statement:
--   For every $L\in\mathbb N$, every linearly ordered set and every array $A$ of length $2^L$, the bitonic network of eq. (1) and Algorithm 1 outputs the sorted version of $A$: the output $R_{L,0}$ is non-decreasing on $\{0,\dots,2^L-1\}$ and is a permutation of $A$.
--
--   With $2^L=2T$ and $A=Q_i$ ordered lexicographically, this is the statement that $R_{i,\log2T,0}$ is the sorted version of $Q_i$. Lemma 4.25 uses it to show that the bootstrapping system simulates the circuit.
--
--   Differences from the source:
--   - generalization: the layers R_{i,k,j} applied to Qᵢ ∈ ({0,…,T−1} × {0,1})^{2T} → any array of length 2^L, L ∈ ℕ, over any linear order; reason: the layers do not depend on the entries; Qᵢ with the lexicographic order and 2^L = 2T is an instance
--   - reading: "for every i ∈ [d+1]" → no index i; reason: the layers R_{i,k,j} exist only for i ∈ [d] and do not depend on i
--   - encoding: "R_{i,log 2T,0} is the sorted version of Qᵢ" → non-decreasing on [0, 2^L) and a permutation of the input; reason: the definition of a sorted version
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Proposition 4.24, p.33 (pdf p.35); Algorithm 1, p.34; eq. (1), p.32

import Mathlib
import Definitions.Def_TargetedSamplers_bitonicNet

namespace TargetedSamplers

/-- Proposition 4.24 (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission,
manuscript sha256 599d0a59…, p.33; Algorithm 1, p.34; eq. (1), p.32). The auxiliary layers
`{R_{i,k,j}}_{k ∈ [log 2T], j ∈ {0,…,k−1}}` sort their inputs in ascending order: `R_{i,log 2T,0}` is the
sorted version of `Qᵢ`.

**Formalization Note** Stated for the network of eq. (1) on any array `A` of length `2^L` over any
linear order (the layers do not depend on `i`; the page's `Qᵢ` has `2^L = 2T` entries in
`{0, …, T−1} × {0,1}`, ordered lexicographically). "Sorted version" is: ascending, and a permutation
of the input. -/
theorem proposition_4_24 {α : Type*} [LinearOrder α] (L : ℕ) (A : ℕ → α) :
    (∀ g h : ℕ, g ≤ h → h < 2 ^ L → bitonicNet L A g ≤ bitonicNet L A h) ∧
    ∃ σ : Equiv.Perm (Fin (2 ^ L)), ∀ g : Fin (2 ^ L), bitonicNet L A g = A (σ g) := by sorry

end TargetedSamplers
