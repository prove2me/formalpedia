-- Prove2me | Theorems.Thm_SalesTrust_Sharing_eq_19
-- name    : SalesTrust.Sharing.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:18.254613+00:00
-- url     : https://prove2.me/theorems/02d9ea09-bd54-497b-b077-ac505b256a2d
-- title:
--   (19), p. 15, with (29) — binding transfers and reduced manufacturer profit with sales information
-- statement:
--   Fix quantities $q_H, q_L$ and assume the standing assumptions $0<p<1$, $V_L<V_H$, $pV_H<V_L$, $0\le\delta<1$.
--
--   1. The constraints $IR^D_L$ (6) and $IC^D_H$ (7) hold with equality if and only if the transfers are those of (29):
--   $$T^{D,e}_L = \pi_R(q_L;L) + \frac{\delta p}{1+\delta p}\,(\Delta(q_L) - \Delta(q^S_L)),\qquad T^{D,e}_H = \pi_R(q_H;H) - \Delta(q_L) + \frac{2\delta p}{1+\delta p}\,(\Delta(q_L) - \Delta(q^S_L)).$$
--   2. At these transfers the manufacturer's expected profit is
--   $$\Pi^{D,e}_M(q_H,q_L) = p\,\pi_R(q_H;H) + (1-p)\,\pi_R(q_L;L) - p\,\Delta(q_L) + \frac{1+p}{1+\delta p}\,\delta p\,(\Delta(q_L) - \Delta(q^S_L)). \tag{19}$$
--
--   Compared with (10), sales information multiplies the dynamic term by $(1+p)/(1+\delta p)$; Proposition 2 maximizes (19).
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 15 (PDF 16), (19); Online Supplement p. 6 (PDF 40), (29)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- (29), Online Supplement p. 6, and (19), p. 15: for any quantities, `IR^D_L` and `IC^D_H`
hold with equality exactly at the transfers (29), and there the manufacturer earns (19). -/
theorem eq_19 (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    (∀ TH TL : ℝ,
      (piR P.VL qL - TL + cont P ⟨qH, TH, qL, TL⟩ = punish P ∧
        piR P.VH qH - TH + cont P ⟨qH, TH, qL, TL⟩ = piR P.VH qL - TL + punish P) ↔
      (TL = TeL P qL ∧ TH = TeH P qH qL)) ∧
    mfrProfit P ⟨qH, TeH P qH qL, qL, TeL P qL⟩ =
      P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL - P.p * gap P qL +
        (1 + P.p) / (1 + P.δ * P.p) * (P.δ * P.p * (gap P qL - gap P (qSL P))) := by sorry

end SalesTrust.Sharing
