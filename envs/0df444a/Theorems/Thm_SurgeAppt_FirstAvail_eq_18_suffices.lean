-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_eq_18_suffices
-- name    : SurgeAppt.FirstAvail.eq_18_suffices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:44.181069+00:00
-- url     : https://prove2.me/theorems/d40f54a5-867c-4286-b4b3-0407a9997623
-- title:
--   Proof of Proposition 1, p. 13 — inequality (18) implies inequalities (17), (19) and (20)
-- statement:
--   Under the standing assumptions of the appointment-scheduling model, let $\overline C(d) = c_sp_{\bar F}^d\beta^d + c_F\varphi(d)$ and $\underline C(d) = c_F\varphi(d)$ be the bounds (15) and (16), with $\varphi$ the bracket of (12). For $1\le d<d'\le D$, if (18) holds,
--
--   $$
--   0\ \ge\ \overline C(d) - \underline C(d'),
--   $$
--
--   then so do
--
--   1. (17): $0\ge \overline C(d) - \overline C(d')$;
--   2. (19): $0\ge \underline C(d) - \overline C(d')$;
--   3. (20): $0\ge \underline C(d) - \underline C(d')$.
--
--   In the proof of Proposition 1 these are the four comparisons of the upper and lower cost bounds at $d$ and $d'$; this step reduces them to the single inequality (18).
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), p. 13, proof of Proposition 1, (17)–(20)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- Proof of Proposition 1, p. 13: for `1 ≤ d < d' ≤ D`, inequality (18) implies inequalities (17),
(19) and (20). -/
theorem eq_18_suffices (P : Params) (hP : P.Standing) (d d' : ℕ) (hd : 1 ≤ d) (hdd' : d < d')
    (hd' : d' ≤ P.D) (h18 : 0 ≥ upper P d - lower P d') :
    0 ≥ upper P d - upper P d' ∧ 0 ≥ lower P d - upper P d' ∧ 0 ≥ lower P d - lower P d' := by sorry

end SurgeAppt.FirstAvail
