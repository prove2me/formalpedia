-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_11
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:33.559672+00:00
-- url     : https://prove2.me/theorems/a34305c4-ca9f-4216-9027-e37a61952553
-- title:
--   Theorem 11 — a lossy TDHF from lossy encryption (Section C.2)
-- statement:
--   Let $l$ be a public polynomial length and let $P$ be an efficient lossy public-key encryption scheme with message space $\{0,1\}^{l(\lambda)}$ that is perfectly correct and secure (Definition 7). Then the Section C.2 function $\mathrm{LTDHF}_l(P)$, with input $x=m\Vert r$ uniform, $\mathrm{Eval}(pk,x)=\mathrm{Enc}(pk,m;r)$, $\mathrm{hEval}(pk,x)=m$, $\mathrm{pInv}=\mathrm{Dec}$ and the key generators of $P$, satisfies
--
--   $$\mathrm{LTDHF}_l(P)\ \text{is an efficient LTDHF with hardcore length }l(\lambda)\text{ that is perfectly correct, mode indistinguishable and statistically lossy}.$$
--
--   This is the reverse half of Theorem 9.
--
--   Differences from the source:
--   - reading: a message or hardcore length l(lambda), polynomially bounded → a public polynomial parameter l (RestrictedDec.PolyParam), computable in unary in uniform polynomial time; reason: base paper.md decision 4; the Section A.2/C.2 evaluation parses x = m||r at l(lambda) and the reduction samples m0, m1 from {0,1}^{l(lambda)}, which a polynomial-time machine can do only when it can compute l(lambda)
--   - reading: Definition 8/12 syntax with efficiently recognizable D_lambda and R_lambda for the constructed function → IsScheme of the constructed function asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: as in the base Theorem 8: the theorem claims correctness and security; pInv is total on strings, the PKE syntax gives no recognizable randomness space, and recognizability is never used
--   - encoding: Eval and hEval (resp. Enc) are one algorithm used with public keys generated in either mode, and hEval outputs an element of {0,1}^{l(lambda)} → one polynomial-time machine agrees with Eval (resp. hEval, Enc) on every key in the support of either key generator, and hEval has length l(lambda) under lossy keys too; reason: Definitions 7 and 12 state the algorithms once for both modes; pInv and Dec are required only for recoverable trapdoors
--   - encoding: every lossy public key in Supp(KGen_los(1^lambda)) → losKeyGen lambda r for every lossy key coin vector r; reason: the same set of keys
--   - encoding: statistical distance (1/2) sum over omega of |Pr[X = omega] - Pr[Y = omega]| → (1/2) times the real tsum over all outcomes of |p(omega) - q(omega)| for PMFs on an arbitrary type; reason: the series is absolutely summable for PMFs, so this is the same number; no finiteness of the outcome space is assumed
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 11, p.53, for the construction of Section C.2, p.50

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_Lossy
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 11, p.53, for the Section C.2 construction, p.50. `Secure` includes
recoverable-mode perfect correctness (Definition 16). -/
theorem theorem_11 :
    ∀ (l : ℕ → ℕ) (P : LPKE), RestrictedDec.PolyParam l → P.IsScheme l →
      P.PerfectlyCorrect l → P.Secure l →
      (ltdhfOfLPKE l P).IsScheme l ∧ (ltdhfOfLPKE l P).Secure l := by sorry

end TrapdoorHCF.CCA2.Supplement
