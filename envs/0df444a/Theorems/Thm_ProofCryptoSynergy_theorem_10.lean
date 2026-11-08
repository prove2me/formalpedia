-- Prove2me | Theorems.Thm_ProofCryptoSynergy_theorem_10
-- name    : ProofCryptoSynergy.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:07:17.913617+00:00
-- url     : https://prove2.me/theorems/6e759923-52e8-4a91-9193-558eb85020e5
-- title:
--   Theorem 10 (subexponential alternative) — no i.o. subexponentially optimal PPS iff every PPS has hard P-uniform unsatisfiable formulas
-- statement:
--   The following are equivalent:
--   1. there is no subexponentially infinitely-often optimal proof system;
--   2. for every PPS $L$ there are a P-uniform sequence of unsatisfiable formulas $\psi_n$ of size $n$ and a constant $c\ge1$ such that for all but finitely many $n$,
--   $$L\text{-size}(\psi_n)\ge 2^{n^{1/c}}.$$
--
--   This is the constructive form of the assumption: it turns the absence of an optimal system into an efficiently generated hard sequence, and it drives Lemma 29.
--
--   Differences from the source:
--   - encoding: propositional formulas of size n; tautologies and unsatisfiable formulas not distinguished → strings of length n read by a total decoding with a formula at every length; length-preserving negation negStr; reason: Lean convention; a formula of size exactly n is what Theorem 10 and Lemma 29 ask for, and no instance changes
--   - encoding: L-size(x) ≤ p(L′-size(x)), with value ∞ if there is no proof; constants c ≥ 1 → every L′-proof π′ of x yields an L-proof π with |π| ≤ 2^{|π′|^{1/c}}; c a positive integer; reason: the same condition, since p is increasing and decreases in c
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Theorem 10, p.19 (PDF 21)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_NoIoSubexpOptimalPPS

namespace ProofCryptoSynergy

/-- **Theorem 10, subexponential alternative** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), p.19 (PDF 21)). There is no subexponentially infinitely-often optimal
proof system iff for every PPS `L` there is a P-uniform sequence of unsatisfiable formulas `ψ_n` of size `n` and some `c ≥ 1`
such that for all but finitely many `n`, `L-size(ψ_n) ≥ 2^{n^{1/c}}`.

**Formalization Note** An `L`-proof of the unsatisfiable `ψ_n` is a proof of the tautology `negStr (ψ_n)` ("we will usually not
distinguish between tautologies and unsatisfiable propositional formulas", p.18). `∞` is avoided by quantifying over proofs. -/
theorem theorem_10 :
    NoIoSubexpOptimalPPS ↔
      ∀ L, IsPPS L → ∃ ψ, IsPUniformUnsat ψ ∧ ∃ c : ℕ, 1 ≤ c ∧
        ∀ᶠ n : ℕ in Filter.atTop, ∀ π, L π = negStr (ψ n) →
          (2 : ℝ) ^ ((n : ℝ) ^ (1 / (c : ℝ))) ≤ (π.length : ℝ) := by sorry

end ProofCryptoSynergy
