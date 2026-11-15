-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_mod_alphabet_lower_bound
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.mod_alphabet_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:47:55.304359+00:00
-- url     : https://prove2.me/theorems/712de78b-fa37-4355-a567-9d27e029adc9
-- title:
--   Theorem 24 — modular counting needs alphabets of size $\Omega(\sqrt q)$
-- statement:
--   For every fixed $c>0$ there are constants $C>0$ and $N\ge1$, depending only on $c$, such that for every $n\ge N$ and every integer $q$ with
--
--   $$2\le q\le(1-c)\,n,$$
--
--   every PSM protocol $P$ for $\mathrm{MOD}_{q,n}(x)=\mathbf 1[\|x\|\equiv0\pmod q]$ that satisfies perfect correctness and support privacy has a party $i$ with
--
--   $$|\mathcal A_i(P)|\ge C\sqrt q,$$
--
--   where $\mathcal A_i(P)$ is the set of messages party $i$ actually sends. The constants are uniform over $q$ and over all protocols.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: every (n,K)-protocol, i.e. declared alphabets with max_i |M_i| ≤ K, has K at least the bound → some actually used local alphabet has at least the bound many messages; reason: the actual alphabet is contained in the declared one, so this conclusion implies the source's for every (n,K)-protocol; trimming unused symbols gives the converse
--   - reading: for 2 ≤ q ≤ (1 − c)n for some constant c > 0 → for every fixed c > 0 (constants depending on c only); reason: 'some constant c' is ambiguous between a fixed unspecified c and every c; the proof's ℓ = min{q−1, n−q} = Ω_c(q) works for every c, and this is the stronger reading, matching Corollary 25
--   - encoding: K = Ω(√q) → ∃ C > 0, ∃ N ≥ 1, ∀ n ≥ N, ∀ q in range, every admissible protocol has an actual alphabet of size ≥ C√q; reason: standard reading of the Ω-lower bound, constants uniform over q and protocols
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 17, Theorem 24 (proof p. 17, paragraph after Theorem 24)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem mod_alphabet_lower_bound :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (1 - c) * n →
      ∀ P : PSM (Fin n), PerfectCorrect P (modFunction q n) →
        SupportPrivate P (modFunction q n) →
        ∃ i : Fin n, C * Real.sqrt q ≤ ((localAlphabet P i).card : ℝ) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
