-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_theorem_8
-- name    : TrapdoorHCF.CCA2.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:52.85221+00:00
-- url     : https://prove2.me/theorems/c92cdef7-a57b-4254-b40c-5052f8fd7ec7
-- title:
--   Theorem 8 — IND-CCA2 encryption gives an ATDHF
-- statement:
--   For every public polynomial message length $l:\mathbb N\to\mathbb N$ and every efficient PKE $P$ over $\{0,1\}^{l(\lambda)}$, suppose $P$ is perfectly correct and IND-CCA2 secure in Definition 2's classical game. Form $F_l(P)$ by Section A.2: sample a uniform message and independent encryption tape, evaluate by encrypting the message on that tape, designate the message, and partially invert by decryption. Then
--
--   $$F_l(P)\text{ is an efficient, perfectly correct and adaptively secure }l(\lambda)\text{-bit TDHF}.$$
--
--   This applies to every public $l$, including the zero length function, and gives the fixed reverse construction of the characterization.
--
--   Differences from the source:
--   - reading: the Section A.2 message length l(lambda) → a public polynomial parameter l, computable in unary in uniform polynomial time; reason: paper.md decision 4; sampling messages and parsing the Section A.2 input require the public length
--   - reading: Definition 8's syntax with efficiently recognizable D_lambda and R_lambda → IsScheme of the Section A.2 TDHF asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: Theorem 8 claims only perfect correctness and ATDHF security; pInv is total on strings (R_lambda may be all strings), the Section 3.2 PKE syntax gives no recognizable randomness space from which D_lambda could be recognized, and recognizability is never used
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: black-box construction or equivalence → security and correctness of the fixed projection, rejection-sampling and/or Section A.2 constructions; reason: paper.md decision 1; Appendix B closes by combining Corollary 7 and Theorem 8; proof-level oracle reductions are left to proofs
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 8, p. 46

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Theorem 8, pp.46–47, and Section A.2, pp.34–35. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem theorem_8 :
    ∀ (l : ℕ → ℕ) (P : RestrictedDec.PKE), RestrictedDec.PolyParam l →
      P.IsScheme l → PKE.PerfectlyCorrect l P → INDCCA2 l P →
      (ofPKE l P).IsScheme l ∧ IsATDHF l (ofPKE l P) := by sorry

end TrapdoorHCF.CCA2
