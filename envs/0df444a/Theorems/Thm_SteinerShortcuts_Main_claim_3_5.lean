-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_5
-- name    : SteinerShortcuts.Main.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:08.630024+00:00
-- url     : https://prove2.me/theorems/eab6f7ba-0204-43de-b76c-454c988ee4ce
-- title:
--   Claim 3.5 — linear representations of the ordering tests
-- statement:
--   In the fixed compatible-pair setup, for $a_1\ne a_2$ the odd test $R^o_{P_1,P_2}$ satisfies (T3′), and for $b_1\ne b_2$ the even test $R^e_{P_1,P_2}$ satisfies (T3′). In each case,
--   $$
--   R^\sigma_{P_1,P_2}(v[p],c)=\operatorname{Upd}(v[p],c)^\top\lambda_\sigma+g_\sigma(\operatorname{layer}(v))
--   \quad(v\in V,\ c\in C).
--   $$
--   These are the source domains of the divided expressions in equation (8). The claim provides both representations used for ordering labels.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - encoding: R odd and R even are introduced only for unequal labels in their respective parities → each representation is conditional on that unequal-label condition; the unused extension of R is zero; reason: no source instance divides by zero; no condition is placed on the other parity
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 19, Claim 3.5 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_5 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    (P.a ≠ Q.a → T3prime L q (testROdd P Q)) ∧
    (P.b ≠ Q.b → T3prime L q (testREven P Q)) := by sorry

end SteinerShortcuts.Main
