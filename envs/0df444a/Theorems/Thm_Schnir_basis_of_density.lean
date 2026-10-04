-- Prove2me | Theorems.Thm_Schnir_basis_of_density
-- name    : Schnir.basis_of_density
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:01:31.833235+00:00
-- url     : https://prove2.me/theorems/4ed167fa-dec1-44dd-92be-c835fb0d16d5
-- title:
--   If $k\,\sigma(A)\ge 1$ then every $n$ is a sum of exactly $k$ elements of $A$
-- statement:
--   Let $A \subseteq \mathbb{Z}_{\ge 0}$ with $0 \in A$, and let $\sigma$ be the Schnirelmann density. If $k$ is a natural number with
--   $$
--   k\,\sigma(A) \;\ge\; 1,
--   $$
--   then every natural number $n$ is a sum of **exactly** $k$ elements of $A$ (repetitions allowed): there is a multiset $t$ with $|t| = k$, all elements of $t$ in $A$, and $\sum_{x \in t} x = n$. The passage from "at most $k$" to "exactly $k$" costs nothing because $0 \in A$ allows padding with zeros.
--
--   Together with the iterated Mann bound $\sigma(kA)\ge\min(1,k\,\sigma(A))$, this is the endpoint of the Schnirelmann density iteration: density $1$ for $kA$ means $kA \supseteq \{1, 2, 3, \dots\}$, and $0 \in kA$ supplies $n = 0$.
--
--   **Formalization Note** The multiset formulation matches the odd-Goldbach campaign statements (`odd_sum_le_6101_primes` and its siblings).
-- source:
--   Standard corollary of Mann's theorem (L. G. Schnirelmann 1930, H. B. Mann 1942); see Nathanson, Additive Number Theory, GTM 165, §7. Uses platform theorem Schnir.mann_iterate.

import Mathlib

namespace Schnir

open Pointwise Classical in
theorem basis_of_density (A : Set ℕ) (hA0 : 0 ∈ A) (k : ℕ)
    (hk : 1 ≤ (k : ℝ) * schnirelmannDensity A) :
    ∀ n : ℕ, ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n := by
  sorry

end Schnir
