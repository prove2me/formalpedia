-- Prove2me | Theorems.Thm_PoWMining_CostStatics_eq_B5
-- name    : PoWMining.CostStatics.eq_B5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:50.683993+00:00
-- url     : https://prove2.me/theorems/94539a0b-03a8-49a5-a356-fcf120fa5835
-- title:
--   (B.5), p. 40 — R(cᵢ + γg)/(R + γg²) = cᵢ + γfᵢ (printed middle term has a sign slip)
-- statement:
--   Under the standing assumptions ($n \ge 2$, $R > 0$, $\gamma \ge 0$, all $c_k > 0$, all $n$ miners active), let $g$ be the aggregate equilibrium hash rate and $f_i = g(R - c_i g)/(R + \gamma g^2)$ the equilibrium hash rate of miner $i$ (B.3). Then
--   $$R\,\frac{c_i + \gamma g}{R + \gamma g^2} = c_i + \gamma f_i.$$
--
--   This identity converts the derivative $\partial f_i/\partial g$ into the form $\frac{g}{R+\gamma g^2}\big(\frac Rg - 2(c_i + \gamma f_i)\big)$ that controls the sign of the indirect sensitivity.
--
--   **Formalization Note.** The paper prints a middle term $c_i - \gamma g\frac{R - c_i g}{R + \gamma g^2}$, which is a sign slip: it equals neither side; with $+$ in place of $-$ it equals both. Only the outer equality, which is what the proof uses, is stated. Miner indices are 0-based (`Fin n`).
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, (B.5), proof of Propositions 4.6 and 4.8

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem eq_B5 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    R * ((c i + γ * gH c γ R) / (R + γ * gH c γ R ^ 2)) = c i + γ * hstar c γ R i := by sorry

end PoWMining.CostStatics
