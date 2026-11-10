-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_6
-- name    : SteinerShortcuts.Main.claim_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:17.531195+00:00
-- url     : https://prove2.me/theorems/f52be7dd-cbde-4303-bbbd-158db2a23f8a
-- title:
--   Claim 3.6 — order of cross-path labels
-- statement:
--   In the fixed compatible-pair setup, if $a_1\ne a_2$, then every odd step of $P_{1,2}$ with label $a_1$ precedes every odd step with label $a_2$, and the order is reversed on $P_{2,1}$. If $b_1\ne b_2$, the analogous statement holds for even labels:
--   $$
--   P_{1,2}:\quad a_1\text{ before }a_2,\ b_1\text{ before }b_2;
--   \qquad
--   P_{2,1}:\quad a_2\text{ before }a_1,\ b_2\text{ before }b_1.
--   $$
--   Each assertion retains its own unequal-label condition. Both parities and both cross-paths are included; empty groups of steps cause no additional restriction.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - encoding: all steps of one label come before all steps of the other → for every pair of such step indices, the first index is strictly smaller; reason: indices count edges from zero while source layers still start at one
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 19, Claim 3.6 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_6 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    (P.a ≠ Q.a → LabelsOrdered R true P.a.val Q.a.val ∧
      LabelsOrdered T true Q.a.val P.a.val) ∧
    (P.b ≠ Q.b → LabelsOrdered R false P.b.val Q.b.val ∧
      LabelsOrdered T false Q.b.val P.b.val) := by sorry

end SteinerShortcuts.Main
