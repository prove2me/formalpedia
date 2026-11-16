-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_3_3
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:51.017196+00:00
-- url     : https://prove2.me/theorems/f4a2326f-9751-4ae4-8067-889a2ea5fe59
-- title:
--   Lemma 3.3 — $\ell$ random perfect matchings miss both crossing events with probability at most $(1/3)^\ell$
-- statement:
--   Let $n\ge4$ be even, and let $A,B$ be nonempty sets forming a partition of $[n]$; fix $i\in A$ and $j\in B$. Sample $\ell$ independent uniformly random perfect matchings $M_1,\dots,M_\ell$ of $[n]$. Then
--
--   $$
--   \Pr\bigl[\text{for every }r\le\ell:\ M_r(i)\notin B\text{ and }M_r(j)\notin A\bigr]\le\Bigl(\frac13\Bigr)^\ell ,
--   $$
--
--   that is, the probability that in none of the matchings $i$ is matched to an element of $B$ or $j$ is matched to an element of $A$ is at most $(1/3)^\ell$.
--
--   Applied to the partition of Lemma 3.1's witness edges, this bounds the probability that Algorithm 2's matchings never test a witness edge.
--
--   **Formalization Note** A perfect matching is a fixed-point-free involution $M$ ($M(v)$ is the partner of $v$); the uniform law on $\ell$-tuples is the counting measure divided by the number of tuples. The partition is given by $A$, with $B$ its complement.
--
--   Differences from the source:
--   - encoding: a partition (A, B) of [n] into nonempty sets with i ∈ A, j ∈ B → A : Finset (Fin n), B = complement of A, i ∈ A, j ∉ A; reason: the same partitions; nonemptiness of A and B is implied by i and j
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 3.3, PDF/printed p.12, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Lemma 3.3, p.12: let `n ≥ 4` be even, let `(A, B)` be a partition of `[n]` into two nonempty
sets (here `B` is the complement of `A`), and fix `i ∈ A`, `j ∈ B`. For `ℓ` independent uniformly
random perfect matchings of `[n]`, the probability that in none of them `i` is matched to an element
of `B` or `j` is matched to an element of `A` is at most `(1/3)^ℓ`. -/
theorem lemma_3_3 (n : ℕ) (hn : 4 ≤ n) (heven : Even n) (A : Finset (Fin n)) (i j : Fin n)
    (hi : i ∈ A) (hj : j ∉ A) (ℓ : ℕ) :
    matchingProb n ℓ (fun M => ∀ r : Fin ℓ, (M r).val i ∈ A ∧ (M r).val j ∉ A) ≤
      (1 / 3 : ℝ) ^ ℓ := by sorry

end QuantumStateIdentity321.Schur.Supplement
