-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_9
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:55.005769+00:00
-- url     : https://prove2.me/theorems/a0719745-0ae5-4846-a335-7670a30a441f
-- title:
--   Theorem 9 (= Theorem 3) — characterization of lossy encryption
-- statement:
--   Perfectly correct and secure lossy trapdoor hardcore functions are black-box equivalent to perfectly correct and secure lossy public-key encryption schemes, through the two constructions of Appendix C. Precisely, both of the following hold.
--
--   1. For every $l$ and every efficient LTDHF $T$ with hardcore length $l(\lambda)$ that is perfectly correct and secure, the Section C.1 scheme $\mathrm{LPKE}(T)$ is an efficient lossy PKE over $\{0,1\}^{l(\lambda)}$ that is perfectly correct and secure.
--   2. For every public polynomial length $l$ and every efficient lossy PKE $P$ over $\{0,1\}^{l(\lambda)}$ that is perfectly correct and secure, the Section C.2 function $\mathrm{LTDHF}_l(P)$ is an efficient LTDHF with hardcore length $l(\lambda)$ that is perfectly correct and secure.
--
--   $$\text{LTDHF}\iff_{BB}\text{lossy PKE}.$$
--
--   Theorem 3 on p.24 is the same statement.
--
--   Differences from the source:
--   - reading: black-box equivalence → correctness and security of the two fixed constructions of Sections C.1 and C.2, as the conjunction of Theorems 10 and 11; reason: base paper.md decision 1 and p.53 ("Combining Theorems 10 and 11 proves Theorem 9"); Theorem 3 on p.24 is the same statement; proof-level oracle reductions are left to proofs
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - reading: Definition 8/12 syntax with efficiently recognizable D_lambda and R_lambda for the constructed function → IsScheme of the constructed function asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: as in the base Theorem 8: the theorem claims correctness and security; pInv is total on strings, the PKE syntax gives no recognizable randomness space, and recognizability is never used
--   - reading: a message or hardcore length l(lambda), polynomially bounded → a public polynomial parameter l (RestrictedDec.PolyParam), computable in unary in uniform polynomial time; reason: base paper.md decision 4; the Section A.2/C.2 evaluation parses x = m||r at l(lambda) and the reduction samples m0, m1 from {0,1}^{l(lambda)}, which a polynomial-time machine can do only when it can compute l(lambda)
--   - reading: Section A.1 decryption returns z XOR ct2 whenever pInv returns z → decryption also returns failure when |z| differs from |ct2|; reason: this happens only for ciphertexts outside C_lambda (ct2 not in {0,1}^{l(lambda)}); on every honest ciphertext the check is vacuous; it makes Dec output elements of M_lambda or failure, as the Section 3.2 syntax requires (SUPPLEMENT.md decision S6)
--   - encoding: Eval and hEval (resp. Enc) are one algorithm used with public keys generated in either mode, and hEval outputs an element of {0,1}^{l(lambda)} → one polynomial-time machine agrees with Eval (resp. hEval, Enc) on every key in the support of either key generator, and hEval has length l(lambda) under lossy keys too; reason: Definitions 7 and 12 state the algorithms once for both modes; pInv and Dec are required only for recoverable trapdoors
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 9, p.47 (identical to Theorem 3, p.24); conclusion p.53

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 9, p.47 (= Theorem 3, p.24), at construction level: Theorem 10 and Theorem 11
("Combining Theorems 10 and 11 proves Theorem 9", p.53). -/
theorem theorem_9 :
    (∀ (l : ℕ → ℕ) (T : LTDHF), T.IsScheme l → T.Secure l →
      (lpkeOfLTDHF T).IsScheme l ∧ (lpkeOfLTDHF T).PerfectlyCorrect l ∧
      (lpkeOfLTDHF T).Secure l) ∧
    (∀ (l : ℕ → ℕ) (P : LPKE), RestrictedDec.PolyParam l → P.IsScheme l →
      P.PerfectlyCorrect l → P.Secure l →
      (ltdhfOfLPKE l P).IsScheme l ∧ (ltdhfOfLPKE l P).Secure l) := by sorry

end TrapdoorHCF.CCA2.Supplement
