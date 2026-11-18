-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D4
-- name    : RealPinwheel.FiveSixths.checked_D4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:01:44.504682+00:00
-- url     : https://prove2.me/theorems/5868a1eb-8e0e-4dcc-916c-762f0203bd52
-- title:
--   Four-task word checks and maximum length
-- statement:
--   Every one of the sixty-nine words of family $W_4$ passes the exact integer finite-window check for its annotated rational density box, and every word has length at most eighteen:
--
--   $$\forall w\in W_4,\quad\operatorname{Checked}(w),\qquad |w|\le18.$$
--
--   The checks consist of the mean and residual-window inequalities, preserving open and closed density endpoints. Checker soundness supplies their all-window scheduling interpretation, while coverage of the real density domain is a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and proof, printed p. 8 (PDF p. 9), Section 4 equation (3), query (4), Table 1 and Lemma 5, printed pp. 9–10 (PDF pp. 10–11), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; D4.txt of https://github.com/grzegorz-gutowski/pinwheel_scheduling/tree/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6

import Definitions.Def_RealPinwheel_FiveSixths_CertificateD4
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D4 : (certificateD4.all fun c => codeCheck 4 (by decide) c && decide ((codeWord 4 (by decide) c).size ≤ 18)) = true := by sorry
