-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_tipping_point
-- name    : ToneAtTop.Diversion.tipping_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:59.963886+00:00
-- url     : https://prove2.me/theorems/a1bcdd50-2967-42dd-91fe-42a8c86b5d9b
-- title:
--   Equation (5), p. 9 — the high-type tipping point
-- statement:
--   Let the diversion model satisfy its standing assumptions and choose $c\in[0,1)$. For any realized temptation $x\ge0$, the high CEO type diverts exactly when $x$ exceeds the tipping point, while the low type diverts exactly when $x>0$:
--
--   $$
--   \mathrm{Noncompliant}(c,x,\eta_H)\iff\frac{\tau}{1-c}<x,
--   \qquad
--   \mathrm{Noncompliant}(c,x,0)\iff 0<x.
--   $$
--
--   This connects the utility comparison to the cutoff used in the expected-loss calculation. At equality the formal model selects compliance, a measure-zero tie left unspecified by the paper.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 9 (PDF 11), §3, eq. (5)

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- Equation (5) identifies the high type's noncompliance cutoff. -/
theorem tipping_point (P : Params) (hS : P.Standing) (c x : ℝ)
    (hc : c ∈ Set.Ico (0 : ℝ) 1) (hx : 0 ≤ x) :
    (Noncompliant P c x P.ηH ↔ tippingPoint P c < x) ∧
    (Noncompliant P c x 0 ↔ 0 < x) := by sorry

end ToneAtTop.Diversion
