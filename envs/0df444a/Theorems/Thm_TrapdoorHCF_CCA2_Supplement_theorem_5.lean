-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_5
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:12.664416+00:00
-- url     : https://prove2.me/theorems/b17c2f61-f8fb-4505-9fc5-d8600aabfd97
-- title:
--   Theorem 5 — the Section A.1 scheme is perfectly correct and IND-CPA secure
-- statement:
--   Let $l:\mathbb N\to\mathbb N$ and let $T$ be an efficient trapdoor hardcore function with hardcore range $\{0,1\}^{l(\lambda)}$ that is perfectly correct and secure (Definitions 9 and 10). Let $\mathrm{KEM}(T)$ be the Section A.1 scheme: keys of $T$; $\mathrm{Enc}(pk,m;r)=(\mathrm{Eval}(pk,r),\mathrm{hEval}(pk,r)\oplus m)$ with $r\leftarrow D_\lambda$; $\mathrm{Dec}(sk,(ct_1,ct_2))=\mathrm{pInv}(sk,ct_1)\oplus ct_2$, or $\perp$. Then
--
--   $$\mathrm{KEM}(T)\ \text{is an efficient PKE over }\{0,1\}^{l(\lambda)}\text{ that is perfectly correct and IND-CPA secure}.$$
--
--   No lower bound on $l$ is needed. This is the forward direction of Theorem 1, given by an explicit construction.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - reading: Section A.1 decryption returns z XOR ct2 whenever pInv returns z → decryption also returns failure when |z| differs from |ct2|; reason: this happens only for ciphertexts outside C_lambda (ct2 not in {0,1}^{l(lambda)}); on every honest ciphertext the check is vacuous; it makes Dec output elements of M_lambda or failure, as the Section 3.2 syntax requires (SUPPLEMENT.md decision S6)
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 5, p.33, for the construction of Section A.1, p.32

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 5, p.33, for the Section A.1 construction, p.32. -/
theorem theorem_5 :
    ∀ (l : ℕ → ℕ) (T : TDHF), T.IsScheme l → IsSecureTDHF l T →
      (kemPKE T).IsScheme l ∧ PKE.PerfectlyCorrect l (kemPKE T) ∧ INDCPA l (kemPKE T) := by sorry

end TrapdoorHCF.CCA2.Supplement
