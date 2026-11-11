-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_corollary_7
-- name    : TrapdoorHCF.CCA2.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:42:08.225926+00:00
-- url     : https://prove2.me/theorems/25c1139d-403f-44f5-989c-edc89d0b5053
-- title:
--   Corollary 7 — CCA2 encryption from ATDHF
-- statement:
--   For every length function $l$ with $l(\lambda)\ge1$ for all sufficiently large $\lambda$ and every efficient, perfectly correct and secure $l(\lambda)$-bit ATDHF $T$, project to its first bit and apply the paper's rejection-sampling encryption construction. The resulting scheme satisfies
--
--   $$C(\pi T)\text{ is an efficient, perfectly correct, IND-CCA2-secure PKE over }\{0,1\}.$$
--
--   This gives the construction-level forward implication of the characterization. Neither the source corollary nor the goal specifies a message length; a one-bit encryption scheme meets their existence claim.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: a hardcore range of length l(lambda) in the forward construction → l(lambda) is at least 1 for all sufficiently large security parameters (some lam0 with 1 <= l(lam) for every lam >= lam0); reason: paper.md decision 3; Lemma 5 takes the first bit, undefined at length zero; the notions are asymptotic, so finitely many zero lengths are allowed (l(lambda) = lambda is covered); the reverse direction still allows zero length
--   - reading: black-box construction or equivalence → security and correctness of the fixed projection, rejection-sampling and/or Section A.2 constructions; reason: paper.md decision 1; Appendix B closes by combining Corollary 7 and Theorem 8; proof-level oracle reductions are left to proofs
--   - reading: Corollary 7 and Theorem 2 assert PKE existence without fixing its message length → the forward construction has the one-bit message space; reason: paper.md decision 2; p.46 already obtains that PKE before the optional Myers–Shelat arbitrary-length transformation, which is not part of the printed claim
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Corollary 7, p. 46

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Corollary 7, p.46. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem corollary_7 :
    ∀ (l : ℕ → ℕ) (T : TDHF), (∃ lam₀, ∀ lam ≥ lam₀, 1 ≤ l lam) →
      T.IsScheme l → IsATDHF l T →
      (cca2Scheme (proj T)).IsScheme (fun _ => 1) ∧
      PKE.PerfectlyCorrect (fun _ => 1) (cca2Scheme (proj T)) ∧
      INDCCA2 (fun _ => 1) (cca2Scheme (proj T)) := by sorry

end TrapdoorHCF.CCA2
