-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_1
-- name    : SteinerShortcuts.Main.claim_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:59.720346+00:00
-- url     : https://prove2.me/theorems/9f4f22ef-0e58-422b-819a-26477fde6009
-- title:
--   Claim 3.1 — transfer of vanishing to cross-paths
-- statement:
--   Fix the compatible critical paths $P_1,P_2$ and cross-paths $P_{1,2},P_{2,1}$ in the optimized construction. Suppose a real test function $F$ is nonnegative at every step of these two cross-paths, vanishes at every step of $P_1,P_2$, and admits the representation $F(p,c)=\operatorname{Upd}(p,c)^\top\lambda+g(\ell)$ on construction vertices. Then
--   $$
--   F(p,c)=0\quad\text{at every step of }P_{1,2}\text{ and }P_{2,1}.
--   $$
--   This transfers a vanishing condition from the critical pair to its two cross-paths. The conclusion uses only the vanishing clause of (T2), not a choice of desired property.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - generalization: the whole (T2) schema, including a desired-property implication → only vanishing on the two critical paths is assumed; reason: the proof of Claim 3.1 uses only this clause, so every source instance satisfies the displayed weaker hypotheses
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 15, Claim 3.1 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

/-- The transfer uses just the critical-path vanishing clause of T2. -/
theorem claim_3_1 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T)
    (F : TestFunction q) (hn : T1prime F R T)
    (hv : Vanishes F (P.route L) ∧ Vanishes F (Q.route L))
    (hl : T3prime L q F) : Vanishes F R ∧ Vanishes F T := by sorry

end SteinerShortcuts.Main
