-- Prove2me | Theorems.Thm_SalesTrust_Sharing_eq_10
-- name    : SalesTrust.Sharing.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:59.07452+00:00
-- url     : https://prove2.me/theorems/132613ca-2c20-4d85-994e-4e7f5272cc88
-- title:
--   (10), p. 11, with (27) — binding transfers and reduced manufacturer profit without sales information
-- statement:
--   Fix quantities $q_H, q_L$ and assume the standing assumptions $0<p<1$, $V_L<V_H$, $pV_H<V_L$, $0\le\delta<1$.
--
--   1. The constraints $IR^D_L$ (6) and $IC^S_H$ (2) hold with equality if and only if the transfers are those of (27):
--   $$T^{D,ne}_L = \pi_R(q_L;L) + \delta p\,(\Delta(q_L) - \Delta(q^S_L)),\qquad T^{D,ne}_H = \pi_R(q_H;H) - \Delta(q_L) + \delta p\,(\Delta(q_L) - \Delta(q^S_L)).$$
--   2. At these transfers the manufacturer's expected profit is
--   $$\Pi^{D,ne}_M(q_H,q_L) = p\,\pi_R(q_H;H) + (1-p)\,\pi_R(q_L;L) - p\,\Delta(q_L) + \delta p\,(\Delta(q_L) - \Delta(q^S_L)). \tag{10}$$
--
--   This reduces the no-sharing program to a maximization over quantities; Proposition 1 maximizes (10).
--
--   **Formalization Note** The page prints $T^{D,ne}_L$ in (27) with an unbalanced parenthesis, "$\delta p(\Delta(q_L) - (\Delta(q^S_L))$"; the balanced reading above is the only one, and it is the one that solves the two equations.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 11 (PDF 12), (10); Online Supplement p. 6 (PDF 40), (27)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- (27), Online Supplement p. 6, and (10), p. 11: for any quantities, `IR^D_L` and `IC^S_H`
hold with equality exactly at the transfers (27), and there the manufacturer earns (10). -/
theorem eq_10 (P : Params) (hS : P.Standing) (qH qL : ℝ) :
    (∀ TH TL : ℝ,
      (piR P.VL qL - TL + cont P ⟨qH, TH, qL, TL⟩ = punish P ∧
        piR P.VH qH - TH = piR P.VH qL - TL) ↔
      (TL = TneL P qL ∧ TH = TneH P qH qL)) ∧
    mfrProfit P ⟨qH, TneH P qH qL, qL, TneL P qL⟩ =
      P.p * piR P.VH qH + (1 - P.p) * piR P.VL qL - P.p * gap P qL +
        P.δ * P.p * (gap P qL - gap P (qSL P)) := by sorry

end SalesTrust.Sharing
