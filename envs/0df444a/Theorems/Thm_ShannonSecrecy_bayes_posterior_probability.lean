-- Prove2me | Theorems.Thm_ShannonSecrecy_bayes_posterior_probability
-- name    : ShannonSecrecy.bayes_posterior_probability
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:31:15.395575+00:00
-- url     : https://prove2.me/theorems/f049b02b-e59c-4d81-aeac-bd3cc28b08c7
-- title:
--   Bayes' theorem for a secrecy system: $P_E(M) = P(M)P_M(E)/P(E)$
-- statement:
--   **Shannon 1949, §10, p. 680 (the Bayes relation).** In a finite secrecy system with a priori message distribution $p$, the probability of a cryptogram and the a posteriori probability of a message are related by
--
--   $$P(E) \;=\; \sum_{M} P(M)\, P_M(E), \qquad\qquad P_E(M) \;=\; \frac{P(M)\, P_M(E)}{P(E)},$$
--
--   where $P(M)$ is the a priori probability of the message $M$; $P_M(E)$ is the conditional probability of the cryptogram $E$ if the message $M$ is chosen, i.e. the sum of the probabilities of all keys which produce $E$ from $M$; $P(E)$ is the probability of obtaining the cryptogram $E$ from any cause; and $P_E(M)$ is the a posteriori probability of the message $M$ if the cryptogram $E$ is intercepted.
--
--   The first identity says that the cryptogram probability decomposes over the possible messages; the second is Bayes' theorem in the form Shannon uses to derive his necessary and sufficient condition for perfect secrecy. Together they are the bookkeeping on which the whole of §10 is based.
--
--   **Formalization Note** The a posteriori probability is defined as the joint probability of the pair (message, cryptogram) divided by the total probability of the cryptogram; the content of the statement is that this joint probability factors as $P(M) P_M(E)$, the message and the key being chosen independently. Both sides are real numbers, and the identity is asserted for every real-valued $p$, including cryptograms of probability zero, where both sides are $0$ under Lean's division convention.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 680 (Part II, §10 Perfect Secrecy, the displayed Bayes formula and the list of its four quantities)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem bayes_posterior_probability
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (p : M → ℝ) (e : E) (m : M) :
    cryptoProb C p e = ∑ m' : M, p m' * msgToCrypto C m' e ∧
      postProb C p e m = p m * msgToCrypto C m e / cryptoProb C p e := by sorry

end ShannonSecrecy
