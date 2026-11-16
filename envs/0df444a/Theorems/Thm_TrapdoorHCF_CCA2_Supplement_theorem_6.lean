-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_Supplement_theorem_6
-- name    : TrapdoorHCF.CCA2.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:33.867918+00:00
-- url     : https://prove2.me/theorems/75c537f9-ed23-44b1-810b-16071fa326ba
-- title:
--   Theorem 6 — the Section A.2 function is a perfectly correct secure TDHF
-- statement:
--   Let $l$ be a public polynomial length and let $P$ be an efficient public-key encryption scheme with message space $\{0,1\}^{l(\lambda)}$ that is perfectly correct and IND-CPA secure (Definitions 1 and 2). Let $F_l(P)$ be the Section A.2 function: its input is $x=m\Vert r$ with $m$ uniform in $\{0,1\}^{l(\lambda)}$ and $r$ uniform encryption randomness, $\mathrm{Eval}(pk,x)=\mathrm{Enc}(pk,m;r)$, $\mathrm{hEval}(pk,x)=m$ and $\mathrm{pInv}=\mathrm{Dec}$. Then
--
--   $$F_l(P)\ \text{is an efficient TDHF with hardcore range }\{0,1\}^{l(\lambda)}\text{ that is perfectly correct and secure}.$$
--
--   This is the reverse direction of Theorem 1, given by an explicit construction.
--
--   Differences from the source:
--   - reading: a message or hardcore length l(lambda), polynomially bounded → a public polynomial parameter l (RestrictedDec.PolyParam), computable in unary in uniform polynomial time; reason: base paper.md decision 4; the Section A.2/C.2 evaluation parses x = m||r at l(lambda) and the reduction samples m0, m1 from {0,1}^{l(lambda)}, which a polynomial-time machine can do only when it can compute l(lambda)
--   - reading: Definition 8/12 syntax with efficiently recognizable D_lambda and R_lambda for the constructed function → IsScheme of the constructed function asserts efficiency, the uniform sampler and output lengths but no recognizability of D_lambda or R_lambda; reason: as in the base Theorem 8: the theorem claims correctness and security; pInv is total on strings, the PKE syntax gives no recognizable randomness space, and recognizability is never used
--   - encoding: a PPT adversary (or pair of PPT algorithms) → one uniform reactive machine with polynomial coins, state, output and total activations (RestrictedDec.Adversary with Valid), run by the base runStage with no oracle; reason: base paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: strings, pairs, inputs x = m||r, randomness and the failure symbol → bit strings, tuple-coded pairs, explicit uniform finite coin vectors, and Option for failure; reason: injective data codes; they change no instance of the source experiments
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 6, p.35, for the construction of Section A.2, pp.34–35

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Supplement_CPA
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2.Supplement

open TrapdoorHCF.CCA2

/-- Theorem 6, p.35, for the Section A.2 construction, pp.34–35. -/
theorem theorem_6 :
    ∀ (l : ℕ → ℕ) (P : RestrictedDec.PKE), RestrictedDec.PolyParam l →
      P.IsScheme l → PKE.PerfectlyCorrect l P → INDCPA l P →
      (ofPKE l P).IsScheme l ∧ IsSecureTDHF l (ofPKE l P) := by sorry

end TrapdoorHCF.CCA2.Supplement
