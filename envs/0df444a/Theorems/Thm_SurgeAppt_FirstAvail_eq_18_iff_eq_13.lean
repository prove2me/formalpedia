-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_eq_18_iff_eq_13
-- name    : SurgeAppt.FirstAvail.eq_18_iff_eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:47.004742+00:00
-- url     : https://prove2.me/theorems/c99d5c6e-6ff4-40b4-a469-6a3fe716f1ea
-- title:
--   Proof of Proposition 1, pp. 13–14 — inequality (18) holds iff $c_s/c_F$ is at most the $(d,d')$ term of (13)
-- statement:
--   Under the standing assumptions of the appointment-scheduling model, write $\varphi(d) = \sum_{l=0}^{d-1}\beta^{l+1}p_Fp_{\bar F}^l + \beta^dp_{\bar F}^d(p_Sp_{F|S}+p_{\bar S}p_{F|\bar S})$ for the discounted failure probability (12), and let
--
--   $$
--   \overline C(d) = c_sp_{\bar F}^d\beta^d + c_F\varphi(d)\quad(15),\qquad \underline C(d) = c_F\varphi(d)\quad(16).
--   $$
--
--   For $1\le d<d'\le D$, inequality (18), $0\ge \overline C(d) - \underline C(d')$, holds if and only if
--
--   $$
--   \frac{c_s}{c_F}\le \big(p_{\bar F}^{d'-d}\beta^{d'-d}-1\big)\big(p_Sp_{F|S}+p_{\bar S}p_{F|\bar S}\big)+\frac{\sum_{i=d}^{d'-1}\beta^{i+1}p_Fp_{\bar F}^i}{p_{\bar F}^d\beta^d},
--   $$
--
--   the $(d,d')$ term of condition (13).
--
--   This is the algebraic step of the proof of Proposition 1 that turns the comparison of a surge booking at $d$ with a base booking at $d'$ into condition (13).
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), pp. 13–14, proof of Proposition 1, (18) and the chain of equivalences ending in (13)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- Proof of Proposition 1, pp. 13–14: for `1 ≤ d < d' ≤ D`, inequality (18),
`0 ≥ (15 at d) − (16 at d')`, holds if and only if `c_s / c_F` is at most the `(d, d')` term of the
right-hand side of (13). -/
theorem eq_18_iff_eq_13 (P : Params) (hP : P.Standing) (d d' : ℕ) (hd : 1 ≤ d) (hdd' : d < d')
    (hd' : d' ≤ P.D) :
    0 ≥ upper P d - lower P d' ↔ P.cs / P.cF ≤ rhs13 P d d' := by sorry

end SurgeAppt.FirstAvail
