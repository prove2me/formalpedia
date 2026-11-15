-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_emaj_alphabet_lower_bound
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.emaj_alphabet_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:47:17.184656+00:00
-- url     : https://prove2.me/theorems/32cab193-61b3-4fea-ac46-e950ec0fb6a7
-- title:
--   Theorem 23 — exact majority needs alphabets of size $\Omega(\sqrt n)$
-- statement:
--   There are constants $c>0$ and $N\ge1$ such that for every $n\ge N$, every PSM protocol $P$ for $\mathrm{EMAJ}_n(x)=\mathbf 1[\|x\|=\lfloor n/2\rfloor]$ that satisfies perfect correctness and support privacy has a party $i$ whose local alphabet satisfies
--
--   $$|\mathcal A_i(P)|\ge c\sqrt n.$$
--
--   Here $\mathcal A_i(P)=\{M_i(b,r):b\in\{0,1\},r\in R\}$ is the set of messages party $i$ actually sends.  Since perfect privacy implies support privacy, the bound also holds for perfect PSMs. The constants are uniform over the shared randomness, the message maps and the decoder.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: every (n,K)-protocol, i.e. declared alphabets with max_i |M_i| ≤ K, has K at least the bound → some actually used local alphabet has at least the bound many messages; reason: the actual alphabet is contained in the declared one, so this conclusion implies the source's for every (n,K)-protocol; trimming unused symbols gives the converse
--   - encoding: K = Ω(√n) → ∃ c > 0, ∃ N ≥ 1, ∀ n ≥ N, every admissible protocol has an actual alphabet of size ≥ c√n; reason: standard reading of the Ω-lower bound, with constants uniform over protocols; all n, even and odd, are covered
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 17, Theorem 23 (proof p. 17, paragraph after Theorem 24)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem emaj_alphabet_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ P : PSM (Fin n), PerfectCorrect P (emajFunction n) →
        SupportPrivate P (emajFunction n) →
        ∃ i : Fin n, c * Real.sqrt n ≤ ((localAlphabet P i).card : ℝ) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
