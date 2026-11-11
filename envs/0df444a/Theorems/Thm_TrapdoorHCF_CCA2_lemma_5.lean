-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_lemma_5
-- name    : TrapdoorHCF.CCA2.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:41.800085+00:00
-- url     : https://prove2.me/theorems/eff76ab3-41d8-410b-be12-7efa0edf1d1e
-- title:
--   Lemma 5 — hardcore-bit projection
-- statement:
--   Let $l:\mathbb N\to\mathbb N$ satisfy $l(\lambda)\ge1$ for all sufficiently large $\lambda$, and let $T$ be an efficient, perfectly correct and secure ATDHF with $l(\lambda)$-bit designated values. Let $\pi T$ preserve keys, input sampling and evaluation, project the designated value to its first bit, and project successful partial-inversion answers to their first bit while preserving failure. Then
--
--   $$\pi T\text{ is an efficient, perfectly correct and secure one-bit ATDHF}.$$
--
--   The fixed projection is the black-box construction of the source; no injectivity condition on evaluation is added.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: a hardcore range of length l(lambda) in the forward construction → l(lambda) is at least 1 for all sufficiently large security parameters (some lam0 with 1 <= l(lam) for every lam >= lam0); reason: paper.md decision 3; Lemma 5 takes the first bit, undefined at length zero; the notions are asymptotic, so finitely many zero lengths are allowed (l(lambda) = lambda is covered); the reverse direction still allows zero length
--   - reading: black-box construction or equivalence → security and correctness of the fixed projection, rejection-sampling and/or Section A.2 constructions; reason: paper.md decision 1; Appendix B closes by combining Corollary 7 and Theorem 8; proof-level oracle reductions are left to proofs
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 5, p. 45

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Lemma 5, pp.45–46. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem lemma_5 (l : ℕ → ℕ) (T : TDHF) (hl : ∃ lam₀, ∀ lam ≥ lam₀, 1 ≤ l lam)
    (hEff : T.IsScheme l) (hSec : IsATDHF l T) :
    (proj T).IsScheme (fun _ => 1) ∧ IsATDHF (fun _ => 1) (proj T) := by sorry

end TrapdoorHCF.CCA2
