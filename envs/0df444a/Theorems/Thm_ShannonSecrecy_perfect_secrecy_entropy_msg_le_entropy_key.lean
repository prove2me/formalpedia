-- Prove2me | Theorems.Thm_ShannonSecrecy_perfect_secrecy_entropy_msg_le_entropy_key
-- name    : ShannonSecrecy.perfect_secrecy_entropy_msg_le_entropy_key
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T19:53:08.051521+00:00
-- url     : https://prove2.me/theorems/8670689b-1f25-4edc-ad6e-77cbda09463b
-- title:
--   Under perfect secrecy, $H(M) \le H(K)$
-- statement:
--   **Shannon 1949, §10, p. 682.** *There is a limit to what can be obtained with a given uncertainty in key: the amount of uncertainty that can be introduced into the solution cannot be greater than the key uncertainty.*
--
--   In a finite secrecy system with perfect secrecy, the entropy of the message is at most the entropy of the key:
--   $$H(M) \;=\; -\sum_{M} P(M)\log P(M) \;\le\; -\sum_{K} P(K)\log P(K) \;=\; H(K),$$
--   for every a priori message distribution $P(\cdot)$. Shannon states the principle in §10 in the special case of the perfect systems just constructed, where the message carries at most $\log n$ bits and "this information can be concealed completely only if the key uncertainty is at least $\log n$", and announces it as the general principle that recurs throughout the paper.
--
--   Combined with the key-counting result, this is the quantitative form of the one-time-pad constraint: concealing $H(M)$ units of message uncertainty costs at least $H(M)$ units of key uncertainty.
--
--   **Formalization Note** Entropy is $H(q) = \sum_a -q(a)\log q(a)$ with the natural logarithm, so both sides are measured in nats; since a change of base multiplies both sides by the same positive constant, the inequality is base-independent. The message distribution is an arbitrary a priori distribution on the finite message set, and the key distribution is the one carried by the system.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, p. 682 (Part II, §10 Perfect Secrecy, the paragraph on key uncertainty following the entropy definitions)

import Definitions.Def_shannon_secrecy_system

namespace ShannonSecrecy

theorem perfect_secrecy_entropy_msg_le_entropy_key
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C) (p : M → ℝ) (hp : IsPMF p) :
    entropy p ≤ entropy C.keyProb := by sorry

end ShannonSecrecy
