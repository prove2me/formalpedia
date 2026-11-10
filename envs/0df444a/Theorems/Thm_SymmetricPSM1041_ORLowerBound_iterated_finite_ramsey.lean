-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_iterated_finite_ramsey
-- name    : SymmetricPSM1041.ORLowerBound.iterated_finite_ramsey
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:14.244567+00:00
-- url     : https://prove2.me/theorems/094ed746-8058-4faf-b6d5-e90178498ac4
-- title:
--   Theorem 15 — one homogeneous subset for every arity
-- statement:
--   Let $\Sigma$ be a finite alphabet and $m\ge1$ an integer. There is an integer $N\ge m$ such that, for every family of colorings $c_k$ assigning a word in $\Sigma^k$ to each $k$-subset of an $N$-element set, for every $1\le k\le m$, there exists a single subset $H$ with
--
--   $$|H|=m,\qquad \forall k\in\{1,\ldots,m\}\ \exists u_k\in\Sigma^k\ \forall S\subseteq H,\ |S|=k:\ c_k(S)=u_k.$$
--
--   The common word may depend on $k$, but the same $H$ serves every arity. The alphabet need not be nonempty; for an empty alphabet there is no such coloring on a nonempty ground set. This theorem supplies simultaneous homogeneity for the agreement lemma.
--
--   Differences from the source:
--   - encoding: an N-element set and words in Σ^k → Fin N and functions Fin k → Alphabet; reason: bijections represent every ground set of size N and every word of length k
--   - encoding: an existential integer N → a witness N≥m; reason: the source construction has this property; increasing a threshold also preserves the conclusion by restriction
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 12, Theorem 15; derivation p. 27, Appendix A.2

import Mathlib

namespace SymmetricPSM1041.ORLowerBound

theorem iterated_finite_ramsey (Alphabet : Type*) [Fintype Alphabet] (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, m ≤ N ∧
      ∀ c : (k : ℕ) → 1 ≤ k → k ≤ m →
        {S : Finset (Fin N) // S.card = k} → (Fin k → Alphabet),
      ∃ H : Finset (Fin N), H.card = m ∧
        ∀ (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m), ∃ word : Fin k → Alphabet,
          ∀ (S : Finset (Fin N)) (hS : S.card = k), S ⊆ H →
            c k hk hkm ⟨S, hS⟩ = word := by sorry

end SymmetricPSM1041.ORLowerBound
