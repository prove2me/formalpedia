-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_theorem_1_1
-- name    : WeightedSetCoverWorstCase.Dynamic.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:29:51.119982+00:00
-- url     : https://prove2.me/theorems/3f07970f-14a0-43be-b76e-f9b3c3656182
-- title:
--   Theorem 1.1 — deterministic fully dynamic weighted set cover: $O(\log n)$-approximation, $O(\log^2 n)$ worst-case recourse, $O(f\,\mathrm{polylog}(fn))$ worst-case update time
-- statement:
--   There are a deterministic program $P$ for the exact real RAM (rational literals, no coins) and a constant $K_A$ such that, for every polynomial aspect exponent $d$, there are constants $K_R,K_T$ and an integer $b$ with the following property. For every weighted set-cover instance (base elements $0..n-1$, $m$ sets with real costs $c>0$, every element in some set, frequency $f$) with $c(s)\le\max(2,n)^dc(s')$ for all $s,s'$, every initial live set $U_0$ and every legal sequence of insertions and deletions, run online (preprocessing on the instance and $U_0$, then one call per update that sees only that update, with persistent memory):
--   - preprocessing halts and its output covers $U_0$;
--   - after every update $i$, the call halts within $K_Tf(1+\log\max(1,fn))^b$ executed instructions, and the maintained family $S_i$ covers the live set $U_i$, has cost $\sum_{s\in S_i}c(s)\le K_A(1+\log\max(1,n))\,\mathrm{OPT}(U_i)$, and recourse $|S_{i-1}\oplus S_i|\le K_R(1+\log\max(1,n))^2$.
--
--   Differences from the source:
--   - encoding: a deterministic fully-dynamic algorithm (no machine named) → a program of the published real RAM ClusterDecomp without coin instructions, run through the online call protocol: preprocessing on the instance and U₀, one call per update writing only that update, persistent memory, the solution read from integer cells −(10 + j); reason: §13 implements the algorithm with exact arithmetic, pointers and charged operations; the protocol makes 'online' and 'update time' precise
--   - generalization: an algorithm (machine constants unrestricted) → the program is admissible: real literals are rational; reason: a stronger claim; an admissible program is in particular a real-RAM program
--   - reading: the standing assumption that C (max/min cost) is at most poly(n) (footnote 1) → for each fixed exponent d, instances with c(s) ≤ max(2, n)^d c(s') for all s, s'; reason: poly(n) with a fixed exponent; max(2, n) avoids a vacuous bound at n ≤ 1
--   - encoding: O(log n)-approximate, O(log² n) worst-case recourse, O(f polylog(fn)) worst-case update time → K_A chosen before d and the instance; K_R, K_T, b chosen for each d before the instance and the sequence; bounds K_A (1 + log max(1,n)) OPT, K_R (1 + log max(1,n))², K_T f (1 + log max(1, f n))^b executed instructions per update call; reason: footnote 1: the approximation does not depend on C; the additive 1 makes the bounds meaningful at n = 1 and fn = 1
--   - reading: the solution S_i ⊆ S must be a set cover of U_i for each i; approximation ratio over all updates i ≥ 1 → feasibility after preprocessing and after every update, approximation and recourse after every update; S_i is the deduplicated family; reason: §6.1's definitions; the internal multiset is deduplicated in the output (§6.1, §13.1.5)
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Theorem 1.1, p. 1 (PDF 4)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_ClusterDecomp_Machine
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Machine

open ClusterDecomp

namespace WeightedSetCoverWorstCase.Dynamic

theorem theorem_1_1 :
    ∃ P : Program, Admissible P ∧ NoCoin P ∧
    ∃ KA : ℝ, ∀ d : ℕ, ∃ KR KT : ℝ, ∃ b : ℕ,
    ∀ (inst : Instance), AspectBound inst d → ∀ U₀ : Finset (Fin inst.u),
      (∃ T, HaltsWithin P (scInit inst U₀) T) ∧
      inst.Covers (outFamily inst (scAfter P inst U₀ [])) U₀ ∧
      ∀ (ups : List (Update inst.u)) (x : Update inst.u), LegalSeq U₀ (ups ++ [x]) →
        (∃ T : ℕ, (T : ℝ) ≤ KT * (inst.freq : ℝ) *
            (1 + Real.log (max 1 ((inst.freq * inst.u : ℕ) : ℝ))) ^ b ∧
          HaltsWithin P (callState (scAfter P inst U₀ ups) (encUpd x)) T) ∧
        inst.Covers (outFamily inst (scAfter P inst U₀ (ups ++ [x]))) (liveAfter U₀ (ups ++ [x])) ∧
        inst.cost0 (outFamily inst (scAfter P inst U₀ (ups ++ [x]))) ≤
          KA * (1 + Real.log (max 1 (inst.u : ℝ))) * inst.OPT0 (liveAfter U₀ (ups ++ [x])) ∧
        (familyRecourse (outFamily inst (scAfter P inst U₀ ups))
            (outFamily inst (scAfter P inst U₀ (ups ++ [x]))) : ℝ) ≤
          KR * (1 + Real.log (max 1 (inst.u : ℝ))) ^ 2 := by sorry

end WeightedSetCoverWorstCase.Dynamic
