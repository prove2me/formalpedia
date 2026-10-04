-- Prove2me | Theorems.Thm_Schnir_basis
-- name    : Schnir.basis
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:01:49.899975+00:00
-- url     : https://prove2.me/theorems/d1f3cf13-25a4-4f26-9cff-88f557ad8e91
-- title:
--   Schnirelmann's basis theorem: positive density $\Rightarrow$ finite additive basis
-- statement:
--   **Schnirelmann's basis theorem** (1930). Let $A \subseteq \mathbb{Z}_{\ge 0}$ contain $0$ and have positive Schnirelmann density, $\sigma(A) > 0$. Then $A$ is an **additive basis of finite order**: there exists $k$ such that every natural number $n$ is a sum of exactly $k$ elements of $A$,
--   $$
--   \forall n \in \mathbb{N}\ \ \exists\, \text{multiset } t:\quad |t| = k,\quad t \subseteq A,\quad \textstyle\sum_{x \in t} x = n.
--   $$
--   Explicitly, $k = \lceil 1/\sigma(A) \rceil$ works.
--
--   This is the theorem for which Schnirelmann introduced his density, and the engine behind Schnirelmann-style additive results on primes: applied to the set of half-shifted primes (whose positive density follows from sieve estimates), it yields that every natural number is a bounded sum of primes — the structural backbone of the odd-Goldbach campaign on this platform. Together with the platform's `Schnir.mann` and `Schnir.mann_iterate` it completes, in content, the Mathlib `Mathlib/Combinatorics/Schnirelmann.lean` TODO: *"Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density."*
--
--   **Formalization Note** Multiset formulation as in the campaign statements; $\sigma$ is Mathlib's `schnirelmannDensity`.
-- source:
--   L. G. Schnirelmann, Über additive Eigenschaften von Zahlen, Math. Ann. 107 (1930), 649–690; textbook treatment in M. B. Nathanson, Additive Number Theory: Inverse Problems of the Theory of Additive Number Theory, GTM 165, §7 (Theorem 7.2). Closes in content the Mathlib TODO in Mathlib/Combinatorics/Schnirelmann.lean line 42.

import Mathlib

namespace Schnir

open Pointwise Classical in
theorem basis (A : Set ℕ) (hA0 : 0 ∈ A) (hσ : 0 < schnirelmannDensity A) :
    ∃ k : ℕ, ∀ n : ℕ, ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n := by
  sorry

end Schnir
