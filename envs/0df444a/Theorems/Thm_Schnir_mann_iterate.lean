-- Prove2me | Theorems.Thm_Schnir_mann_iterate
-- name    : Schnir.mann_iterate
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:01:29.572984+00:00
-- url     : https://prove2.me/theorems/f5537fd9-dc43-46da-971b-52d6ea5ae5d5
-- title:
--   Iterated Mann: $\sigma(kA)\ge\min(1,k\,\sigma(A))$
-- statement:
--   Mann's theorem iterated. Let $A \subseteq \mathbb{Z}_{\ge 0}$ with $0 \in A$, let $\sigma$ be the Schnirelmann density, and let $k \ge 0$. Write $kA$ for the set of sums of exactly $k$ elements of $A$, repetitions allowed:
--   $$
--   kA = \Bigl\{ \textstyle\sum_{x \in t} x : t \text{ a multiset of cardinality } k,\ \text{all elements in } A \Bigr\}.
--   $$
--   Then
--   $$
--   \sigma(kA) \;\ge\; \min\bigl(1,\; k\,\sigma(A)\bigr).
--   $$
--   This is the form in which Mann's inequality $\sigma(X+Y)\ge\min(1,\sigma X+\sigma Y)$ is consumed: it replaces the weaker product iteration $\sigma(kA)\ge 1-(1-\sigma(A))^k$ that underlies the $6101$-primes entry of the odd-Goldbach campaign. Once $k\,\sigma(A)\ge 1$ the bound reads $\sigma(kA)=1$, i.e. $kA$ contains every positive integer.
--
--   **Formalization Note** $kA$ is the set builder in the statement (multiset sums of cardinality exactly $k$); $\sigma$ is Mathlib's `schnirelmannDensity` with classical decidability.
-- source:
--   Iteration of H. B. Mann's theorem (1942); see M. B. Nathanson, Additive Number Theory: Inverse Problems of Additive Number Theory, GTM 165, §7.4, and Nathanson, arXiv:2407.12253 §2. Direct companion of platform theorem Schnir.mann.

import Mathlib

namespace Schnir

open Pointwise Classical in
theorem mann_iterate (A : Set ℕ) (hA0 : 0 ∈ A) (k : ℕ) :
    min 1 ((k : ℝ) * schnirelmannDensity A) ≤
      schnirelmannDensity {n | ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n} := by
  sorry

end Schnir
