-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_10
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:37.747596+00:00
-- url     : https://prove2.me/theorems/2de0fadb-4a97-490c-8680-496bcf027d3e
-- title:
--   Theorem 10 — lossy encryption from a lossy TDHF (Section C.1)
-- statement:
--   Let $l:\mathbb N\to\mathbb N$ and let $T$ be an efficient lossy trapdoor hardcore function with hardcore length $l(\lambda)$ that is perfectly correct and secure (Definitions 12–16). Then the Section C.1 scheme $\mathrm{LPKE}(T)$, which encrypts $m$ as $(\mathrm{Eval}(pk,X),\mathrm{hEval}(pk,X)\oplus m)$ with $X\leftarrow D_\lambda$ and uses the key generators of $T$, satisfies
--
--   $$\mathrm{LPKE}(T)\ \text{is an efficient lossy PKE over }\{0,1\}^{l(\lambda)}\text{ that is perfectly correct, mode indistinguishable and ciphertext lossy}.$$
--
--   This is the forward half of Theorem 9.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces D_lambda → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: base paper.md decision 5; every source input space is an instance, so the hypothesis class only grows; the constructions and experiments use only sampling
--   - reading: Section A.1 decryption returns z XOR ct2 whenever pInv returns z → decryption also returns failure when |z| differs from |ct2|; reason: this happens only for ciphertexts outside C_lambda (ct2 not in {0,1}^{l(lambda)}); on every honest ciphertext the check is vacuous; it makes Dec output elements of M_lambda or failure, as the Section 3.2 syntax requires (SUPPLEMENT.md decision S6)
--   - encoding: Eval and hEval (resp. Enc) are one algorithm used with public keys generated in either mode, and hEval outputs an element of {0,1}^{l(lambda)} → one polynomial-time machine agrees with Eval (resp. hEval, Enc) on every key in the support of either key generator, and hEval has length l(lambda) under lossy keys too; reason: Definitions 7 and 12 state the algorithms once for both modes; pInv and Dec are required only for recoverable trapdoors
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 10, p.49, for the construction of Section C.1, pp.47–48

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 10, p.49, for the Section C.1 construction, pp.47–48. -/
theorem theorem_10 :
    ∀ (l : ℕ → ℕ) (T : LTDHF), T.IsScheme l → T.Secure l →
      (lpkeOfLTDHF T).IsScheme l ∧ (lpkeOfLTDHF T).PerfectlyCorrect l ∧
      (lpkeOfLTDHF T).Secure l := by sorry

end TrapdoorHCF.CCA2.Supplement
