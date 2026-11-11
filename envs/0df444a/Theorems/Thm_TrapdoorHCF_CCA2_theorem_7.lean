-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_theorem_7
-- name    : TrapdoorHCF.CCA2.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:51.767784+00:00
-- url     : https://prove2.me/theorems/86722488-f741-45e2-8aa2-13a88d2cb712
-- title:
--   Theorem 7 — one-bit CCA2 encryption from ATDHF
-- statement:
--   For every efficient, perfectly correct and secure one-bit ATDHF $T$, form $C(T)$ by the exact construction on pp.36–37: encrypt a one-bit message using the first matching candidate among $\lambda$ independent samples, or return the flagged message when no candidate matches. Then
--
--   $$C(T)\text{ is an efficient, perfectly correct, IND-CCA2-secure PKE over }\{0,1\}.$$
--
--   Security is the classical exact-challenge-exclusion game of Definition 2, including unrestricted decryption before the challenge. The conclusion contains all three properties, without assuming any of them for the constructed scheme.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: black-box construction or equivalence → security and correctness of the fixed projection, rejection-sampling and/or Section A.2 constructions; reason: paper.md decision 1; Appendix B closes by combining Corollary 7 and Theorem 8; proof-level oracle reductions are left to proofs
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 7, p. 36

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Theorem 7, pp.36–37. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem theorem_7 (T : TDHF) (hEff : T.IsScheme (fun _ => 1))
    (hSec : IsATDHF (fun _ => 1) T) :
    (cca2Scheme T).IsScheme (fun _ => 1) ∧
    PKE.PerfectlyCorrect (fun _ => 1) (cca2Scheme T) ∧
    INDCCA2 (fun _ => 1) (cca2Scheme T) := by sorry

end TrapdoorHCF.CCA2
