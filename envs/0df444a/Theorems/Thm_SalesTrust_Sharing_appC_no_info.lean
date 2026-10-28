-- Prove2me | Theorems.Thm_SalesTrust_Sharing_appC_no_info
-- name    : SalesTrust.Sharing.appC_no_info
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:57.591328+00:00
-- url     : https://prove2.me/theorems/67629eeb-0192-418b-9bb8-c309279e6900
-- title:
--   Appendix C, Online Supplement p. 11 — without sales information, IR^D_H and IC^S_L are slack at the transfers (27)
-- statement:
--   Assume the standing assumptions and let $0 < q_L < q_H$. Take the transfers $T^{D,ne}_H, T^{D,ne}_L$ of (27) (the ones that make $IR^D_L$ and $IC^S_H$ bind). Then the two remaining constraints of the no-sharing program hold strictly: the high-state dynamic participation constraint
--   $$\pi_R(q_H;H) - T^{D,ne}_H + \tfrac{\delta}{1-\delta}\,\Pi_R \ >\ \tfrac{\delta}{1-\delta}\,p\Delta(q^S_L)$$
--   and the low-state static incentive constraint
--   $$\pi_R(q_L;L) - T^{D,ne}_L \ >\ \pi_R(q_H;L) - T^{D,ne}_H,$$
--   where $\Pi_R$ is the retailer's expected profit at the menu $\{(q_H, T^{D,ne}_H), (q_L, T^{D,ne}_L)\}$.
--
--   Together with (10) this shows that the relaxed program with only $IR^D_L$ and $IC^S_H$ has the same solution as the full program.
--
--   **Formalization Note** The hypothesis $q_L > 0$ is added: the page's slack is $\Delta(q_L) = (V_H - V_L)q_L$, which the paper calls positive by its assumption $\pi_R(q;H) > \pi_R(q;L)$; in the linear model that holds exactly for $q > 0$.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), Appendix C, Online Supplement p. 11 (PDF 45), 'Repeated game with no ex-post information', (41)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- Appendix C, Online Supplement p. 11: without sales information, at the transfers (27)
and for `0 < q_L < q_H`, the constraints `IR^D_H` (6) and `IC^S_L` (2) hold strictly. -/
theorem appC_no_info (P : Params) (hS : P.Standing) (qH qL : ℝ) (hqL : 0 < qL) (hlt : qL < qH) :
    punish P < piR P.VH qH - TneH P qH qL + cont P ⟨qH, TneH P qH qL, qL, TneL P qL⟩ ∧
      piR P.VL qH - TneH P qH qL < piR P.VL qL - TneL P qL := by sorry

end SalesTrust.Sharing
