-- Prove2me | Theorems.Thm_SalesTrust_Sharing_appC_info
-- name    : SalesTrust.Sharing.appC_info
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:06.545962+00:00
-- url     : https://prove2.me/theorems/885e2fea-af11-4c13-8a13-cd47a3c17850
-- title:
--   Appendix C, Online Supplement pp. 11–12 — with sales information, IR^D_H and IC^D_L are slack at the transfers (29)
-- statement:
--   Assume the standing assumptions and let $q^S_L < q_L < q_H$. Take the transfers $T^{D,e}_H, T^{D,e}_L$ of (29) (the ones that make $IR^D_L$ and $IC^D_H$ bind), and let $\Pi_R$ be the retailer's expected profit at the menu $\{(q_H, T^{D,e}_H), (q_L, T^{D,e}_L)\}$. Then the two remaining constraints of the sharing program hold strictly:
--   $$\pi_R(q_H;H) - T^{D,e}_H + \tfrac{\delta}{1-\delta}\,\Pi_R \ >\ \tfrac{\delta}{1-\delta}\,p\Delta(q^S_L),$$
--   $$\pi_R(q_L;L) - T^{D,e}_L + \tfrac{\delta}{1-\delta}\,\Pi_R \ >\ \pi_R(q_H;L) - T^{D,e}_H + \tfrac{\delta}{1-\delta}\,p\Delta(q^S_L).$$
--
--   Together with (19) this shows that the relaxed program with only $IR^D_L$ and $IC^D_H$ has the same solution as the full sharing program.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), Appendix C, Online Supplement pp. 11–12 (PDF 45–46), 'Repeated game with ex-post information', (41)–(43)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- Appendix C, Online Supplement pp. 11–12: with sales information, at the transfers (29)
and for `q^S_L < q_L < q_H`, the constraints `IR^D_H` (6) and `IC^D_L` (7) hold strictly. -/
theorem appC_info (P : Params) (hS : P.Standing) (qH qL : ℝ) (hqL : qSL P < qL) (hlt : qL < qH) :
    punish P < piR P.VH qH - TeH P qH qL + cont P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ ∧
      piR P.VL qH - TeH P qH qL + punish P <
        piR P.VL qL - TeL P qL + cont P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ := by sorry

end SalesTrust.Sharing
