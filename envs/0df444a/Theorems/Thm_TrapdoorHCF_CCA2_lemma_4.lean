-- Prove2me | Theorems.Thm_TrapdoorHCF_CCA2_lemma_4
-- name    : TrapdoorHCF.CCA2.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T19:42:05.051865+00:00
-- url     : https://prove2.me/theorems/5f97cbca-8eb2-4353-8147-7347c6fa9e65
-- title:
--   Lemma 4 — hidden-candidate queries are negligible
-- statement:
--   Let $T$ be an efficient, perfectly correct, secure one-bit ATDHF, and let $A=(A_1,A_2)$ be any uniform PPT adversary against its constructed encryption scheme. Run $A_1$ with genuine decryption access to obtain its two valid one-bit messages and state. Sample a fair challenge bit $b$, $\lambda$ independent inputs $X_i$, and evaluations $Y_i$. The candidate strings $Z_i$ are either all real designated bits or independent uniform bits. Let $I$ be the first candidate matching $m_b$, or $\perp$ when none matches. If selected, the challenge is $(Y_I,0)$ and $H_I=\{Y_j:j\ne I\}\setminus\{Y_I\}$; otherwise the challenge is $(m_b,1)$ and all candidate evaluations form $H_I$.
--
--   In both experiments, $A_2$ has genuine decryption restricted only at the exact challenge. Let $\mathrm{Bad}$ mean that it submits $(y,0)$ with $y\in H_I$. Both conclusions hold:
--
--   $$\lambda\longmapsto\Pr[\mathrm{Bad}\mid\delta=\mathrm{real}]\text{ is negligible},\qquad\lambda\longmapsto\Pr[\mathrm{Bad}\mid\delta=\mathrm{rand}]\text{ is negligible}.$$
--
--   Invalid challenge messages abort as in Definition 2. The event records queries even if a later activation exhausts the budget; selected-value collisions are excluded from the hidden set.
--
--   Differences from the source:
--   - generalization: uniform sampling from efficiently recognizable input spaces → polynomial-time input samplers on uniform coins, with the input space their range and no recognizability condition; reason: paper.md decision 5; every source space is an instance, and the constructions and experiments use only sampling
--   - reading: perfectly correct and secure ATDHF → Definition 11: perfect correctness conjoined with negligible adaptive distinguishing advantage; reason: paper.md decision 6; Definition 11 explicitly presupposes perfect correctness
--   - encoding: a pair of PPT oracle algorithms → one uniform reactive machine with polynomial coins, state, output and total activations, carrying state across the challenge; reason: paper.md decision 7; either presentation simulates the other with a polynomial budget; no advice or unbounded adversaries are introduced
--   - encoding: finite sets, strings, pairs, randomness and failure symbol → bit strings and tuple-coded lists, explicit uniform finite coin vectors, flag-prefixed ciphertexts, and Option for failure; reason: these injective data codes preserve the source experiments; duplicates do not affect membership and malformed ciphertexts return failure
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Lemma 4, p. 40

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Auxiliary
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- Lemma 4, p.40. The sampler and uniform PPT conventions are explicit in the imported definitions. -/
theorem lemma_4 (T : TDHF) (hEff : T.IsScheme (fun _ => 1))
    (hSec : IsATDHF (fun _ => 1) T) (A : RestrictedDec.Adversary) (hA : A.Valid) :
    NoisyOWMPC.Negligible (fun lam => prOne (expBad T A false lam)) ∧
    NoisyOWMPC.Negligible (fun lam => prOne (expBad T A true lam)) := by sorry

end TrapdoorHCF.CCA2
