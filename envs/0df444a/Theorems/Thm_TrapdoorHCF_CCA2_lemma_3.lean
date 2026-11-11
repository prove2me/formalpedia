-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_lemma_3
-- name    : TrapdoorHCF.CCA2.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:41:50.263345+00:00
-- url     : https://prove2.me/theorems/77768f66-6d5c-4f79-abae-eab1e686d3dc
-- title:
--   Lemma 3 — multi-sample adaptive pseudorandomness
-- statement:
--   Let $T$ be an efficient, perfectly correct, secure one-bit ATDHF. Let $q$ be any public polynomial parameter and let $D=(D_1,D_2)$ be any uniform PPT oracle adversary. Generate keys, run $D_1$ with full partial-inversion access, then independently sample $q(\lambda)$ inputs $X_i$ and their evaluations $Y_i$. Give $D_2$ the state and ordered pairs $(Y_i,Z_i)$, with an oracle refusing every $Y_i$ and otherwise returning partial inversion. In the real experiment $Z_i=\operatorname{hEval}(pk,X_i)$; in the random experiment the $Z_i$ are independent uniform bits. Then
--
--   $$\lambda\longmapsto\left|\Pr[D_{\rm real}=1]-\Pr[D_{\rm rand}=1]\right|\quad\text{is negligible}.$$
--
--   The claim includes $q(\lambda)=0$ and arbitrary evaluation collisions, and supplies the multi-sample security target used in the encryption theorem.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - reading: a polynomially bounded sample count q(lambda) → a public polynomial parameter q; reason: paper.md decision 8; the p.38–39 reduction samples a uniform index in the public candidate list; q=0 is retained
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 3, p. 38

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Lemma 3, p.38. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem lemma_3 (T : TDHF) (hEff : T.IsScheme (fun _ => 1))
    (hSec : IsATDHF (fun _ => 1) T) (q : ℕ → ℕ) (hq : RestrictedDec.PolyParam q)
    (D : RestrictedDec.Adversary) (hD : D.Valid) :
    NoisyOWMPC.Negligible
      (advantage (expMulti T q D false) (expMulti T q D true)) := by sorry

end TrapdoorHCF.CCA2
