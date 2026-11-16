-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_theorem_D_1
-- name    : TwoMasterRoommates.Capped.Supplement.theorem_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:36:13.402241+00:00
-- url     : https://prove2.me/theorems/675efe1f-4e28-4b55-93bb-4cabbede6efc
-- title:
--   Theorem D.1 (= Theorem 1.2) — the reward-threshold problem is NP-complete with a flat and a strict master
-- statement:
--   Consider even complete roommate instances $V=A\cup B$ in which every $A$ observer is indifferent among all other agents, every $B$ observer follows the same whole strict master $b$, and all $A$ identities precede all $B$ identities in $b$. Rewards are given on unordered pairs, independently of the preferences. The reward-threshold problem asks, for such an instance, rewards $w$ and a threshold $T$, whether some weakly stable perfect matching $M$ has
--
--   $$w(M)\ge T.$$
--
--   The theorem has four parts.
--
--   1. With the signed alphabet $w(AA)=0$, $w(AB)\in\{-3,0\}$, $w(BB)\in\{-3,1,4\}$ the problem is NP-complete.
--   2. With the signed alphabet, every NP language reduces to it by a polynomial-time reduction whose every output is an instance that has a weakly stable perfect matching.
--   3. With all rewards in $\{0,3,4,7\}$ the problem is NP-complete.
--   4. With all rewards in $\{0,3,4,7\}$, the same holds as in part 2.
--
--   Hardness therefore comes from the independent reward and not from deciding whether a stable matching exists, which is polynomial for two masters by the mission's goal.
--
--   Differences from the source:
--   - encoding: the decision problem on instances, rewards and a threshold → a language of binary codes; strings that are not codes of domain instances with alphabet rewards are outside it; reason: the standard convention for a decision problem on structured inputs; the codes are prefix-free and polynomial-time decodable
--   - encoding: NP-complete → CookPvsNP.NPComplete: membership in NP and a polynomial-time many-one reduction from every NP language over every finite nonempty alphabet; reason: Cook's Definition 4, the standard notion
--   - reading: 'The reduction produces instances that always have a weakly stable perfect matching', said in D.1 of the signed reduction and in Theorem 1.2 of the {0,3,4,7} reduction → for both alphabets, every NP language has a polynomial-time reduction all of whose outputs are domain instances with alphabet rewards that have a weakly stable perfect matching; reason: D.1 and Theorem 1.2 state the same theorem; the shift on p. 25 preserves stability, and composing with any reduction to 3-SAT keeps the property
--   - encoding: rewards on original unordered pairs → a function on Sym2 (Fin n) whose values on the diagonal are not encoded and not constrained; reason: a diagonal pair is never an edge of a perfect matching
--   - encoding: every A observer indifferent among all other agents, every B observer following one whole strict master b with all A identities first, no caps → an Instance ℤ n with every cap ⊤, the master a constant on all identities (own entries included), and b injective with b(x) < b(y) for x ∈ A, y ∈ B; reason: an observer's own entry is never compared (Blocks requires u ≠ v and a perfect matching has no fixed point), and integer ranks represent every flat or strict order on a finite set
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 23 (PDF p. 24), Theorem D.1 (= Theorem 1.2, p. 2, PDF p. 3)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_Hardness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Theorem D.1 (= Theorem 1.2), Bin Yu, STOC 2027 submission #225, p. 23 (PDF 24): in the
flat/strict domain the reward-threshold problem is NP-complete with the signed alphabet
`w(AA) = 0`, `w(AB) ∈ {−3, 0}`, `w(BB) ∈ {−3, 1, 4}` and with the alphabet `{0, 3, 4, 7}`;
for both, every NP language reduces to it by a polynomial-time reduction whose outputs always have
a weakly stable perfect matching. -/
theorem theorem_D_1 :
    (CookPvsNP.NPComplete (ThreshLang signedRule) ∧ StableOutputReductions signedRule) ∧
    (CookPvsNP.NPComplete (ThreshLang (setRule alphabetD1)) ∧
      StableOutputReductions (setRule alphabetD1)) := by sorry

end TwoMasterRoommates.Capped.Supplement
