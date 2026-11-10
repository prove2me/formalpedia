-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_constant_alphabet_or_impossible
-- name    : SymmetricPSM1041.ORLowerBound.constant_alphabet_or_impossible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:38.642768+00:00
-- url     : https://prove2.me/theorems/d37b2dd6-4229-44e2-94df-b7f0373daa05
-- title:
--   Theorem 19 — bounded alphabets cannot compute OR
-- statement:
--   For every fixed integer $K\ge0$ there is a positive integer $N$, uniform over all finite shared-randomness sizes, message maps, local alphabets and decoders, such that for every $n\ge N$ and every PSM protocol $P$,
--
--   $$\bigl(\forall i\in[n],\ |\mathcal A_i(P)|\le K\bigr)\ \Longrightarrow\ \neg\bigl(\operatorname{PerfectCorrect}(P,\mathrm{OR}_n)\land\operatorname{SupportPrivate}(P,\mathrm{OR}_n)\bigr).$$
--
--   Here $\mathcal A_i(P)$ is the set of messages actually used by party $i$. Trimming unused declared symbols makes this exactly the source's exclusion of $(n,K)$-protocols. The bound covers $K=0,1$ and arbitrary asymmetric protocols. It concerns local alphabet sizes, and must be lifted separately to bound worst-case actual transcript length.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: declared local alphabets of size at most K → actual message-image alphabets of size at most K; reason: unused symbols can be removed and the decoder restricted, preserving both hypotheses and all transcript lengths
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 14, Theorem 19 (proof pp. 15–16)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound

theorem constant_alphabet_or_impossible (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ P : PSM (Fin n),
      (∀ i, (localAlphabet P i).card ≤ K) →
      ¬ (PerfectCorrect P orFunction ∧ SupportPrivate P orFunction) := by sorry

end SymmetricPSM1041.ORLowerBound
