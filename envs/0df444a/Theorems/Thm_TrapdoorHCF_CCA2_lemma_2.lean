-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_lemma_2
-- name    : TrapdoorHCF.CCA2.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:54.07486+00:00
-- url     : https://prove2.me/theorems/f546fc11-d6aa-4aeb-957a-53825bc22f34
-- title:
--   Lemma 2 — unpredictability of a fresh evaluation
-- statement:
--   Let $T$ be an efficient one-bit ATDHF, perfectly correct and adaptively secure, and let $B$ be any uniform PPT oracle machine. At security parameter $\lambda$, generate $(pk,sk)$ and run $B$ with input $(1^\lambda,pk)$ and unrestricted access to $\operatorname{pInv}(sk,\cdot)$, obtaining a polynomial-size set $S$. Independently sample $X$ from the input distribution and set $Y=\operatorname{Eval}(pk,X)$. Then
--
--   $$\lambda\longmapsto\Pr[Y\in S]\quad\text{is negligible}.$$
--
--   The probability includes key generation, the machine's coins, and the fresh sample. This isolates the unpredictability property needed for the encryption construction.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 2, p. 37

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Lemma 2, p.37. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem lemma_2 (T : TDHF) (hEff : T.IsScheme (fun _ => 1))
    (hSec : IsATDHF (fun _ => 1) T) (B : RestrictedDec.Adversary) (hB : B.Valid) :
    NoisyOWMPC.Negligible (fun lam => prOne (expFresh T B lam)) := by sorry

end TrapdoorHCF.CCA2
