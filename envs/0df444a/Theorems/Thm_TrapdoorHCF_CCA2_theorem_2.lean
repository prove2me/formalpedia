-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_theorem_2
-- name    : TrapdoorHCF.CCA2.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:38.677636+00:00
-- url     : https://prove2.me/theorems/0d74bed4-3a58-401a-9a3d-4391f1d94466
-- title:
--   Theorem 2 — characterization of chosen-ciphertext security
-- statement:
--   Adaptive trapdoor hardcore functions and classical chosen-ciphertext-secure public-key encryption are equivalent through the following fixed constructions, with perfect correctness in both directions. Write $\pi T$ for first-bit projection, $C$ for the pp.36–37 encryption construction, and $F_l$ for the Section A.2 construction.
--
--   For every $l:\mathbb N\to\mathbb N$ with $l(\lambda)\ge1$ for all sufficiently large $\lambda$ and every efficient $l(\lambda)$-bit TDHF $T$,
--
--   $$T\text{ perfectly correct and ATDHF secure}\ \Longrightarrow\ C(\pi T)\text{ efficient, perfectly correct and IND-CCA2 secure over }\{0,1\}.$$
--
--   For every public polynomial parameter $l$ and every efficient PKE $P$ over $\{0,1\}^{l(\lambda)}$,
--
--   $$P\text{ perfectly correct and IND-CCA2 secure}\ \Longrightarrow\ F_l(P)\text{ efficient, perfectly correct and ATDHF secure}.$$
--
--   Both clauses quantify over every input scheme. The reverse clause allows zero message length. The security games use the same uniform PPT adversary class and reject exactly the full challenge string after the challenge, even when the CCA2 messages coincide. These construction-level implications give the existence characterization stated in the source.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: a hardcore range of length l(lambda) in the forward construction → l(lambda) is at least 1 for all sufficiently large security parameters (some lam0 with 1 <= l(lam) for every lam >= lam0); reason: paper.md decision 3; Lemma 5 takes the first bit, undefined at length zero; the notions are asymptotic, so finitely many zero lengths are allowed (l(lambda) = lambda is covered); the reverse direction still allows zero length
--   - reading: the Section A.2 message length l(lambda) → a public polynomial parameter l, computable in unary in uniform polynomial time; reason: paper.md decision 4; sampling messages and parsing the Section A.2 input require the public length
--   - reading: Definition 8's syntax with efficiently recognizable D_lambda and R_lambda → IsScheme of the Section A.2 TDHF asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: Theorem 8 claims only perfect correctness and ATDHF security; pInv is total on strings (R_lambda may be all strings), the Section 3.2 PKE syntax gives no recognizable randomness space from which D_lambda could be recognized, and recognizability is never used
--   - reading: black-box construction or equivalence → security and correctness of the fixed projection, rejection-sampling and/or Section A.2 constructions; reason: paper.md decision 1; Appendix B closes by combining Corollary 7 and Theorem 8; proof-level oracle reductions are left to proofs
--   - reading: Corollary 7 and Theorem 2 assert PKE existence without fixing its message length → the forward construction has the one-bit message space; reason: paper.md decision 2; p.46 already obtains that PKE before the optional Myers–Shelat arbitrary-length transformation, which is not part of the printed claim
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 2, p. 18

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Theorem 2, p.18; its two construction-level clauses are Corollary 7 and Theorem 8. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem theorem_2 :
    (∀ (l : ℕ → ℕ) (T : TDHF), (∃ lam₀, ∀ lam ≥ lam₀, 1 ≤ l lam) →
      T.IsScheme l → IsATDHF l T →
      (cca2Scheme (proj T)).IsScheme (fun _ => 1) ∧
      PKE.PerfectlyCorrect (fun _ => 1) (cca2Scheme (proj T)) ∧
      INDCCA2 (fun _ => 1) (cca2Scheme (proj T))) ∧
    (∀ (l : ℕ → ℕ) (P : RestrictedDec.PKE), RestrictedDec.PolyParam l →
      P.IsScheme l → PKE.PerfectlyCorrect l P → INDCCA2 l P →
      (ofPKE l P).IsScheme l ∧ IsATDHF l (ofPKE l P)) := by sorry

end TrapdoorHCF.CCA2
