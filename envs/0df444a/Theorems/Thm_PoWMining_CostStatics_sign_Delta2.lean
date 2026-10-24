-- Prove2me | Theorems.Thm_PoWMining_CostStatics_sign_Delta2
-- name    : PoWMining.CostStatics.sign_Delta2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:08.453459+00:00
-- url     : https://prove2.me/theorems/1ddd8c9f-89cb-491a-9724-729d20b33d1c
-- title:
--   p. 40, proof of Proposition 4.6 — Δᵢ,₂ > 0 ⟺ cᵢ + γfᵢ = (R/g)(1 − fᵢ/g) > R/(2g) ⟺ fᵢ/g < 1/2
-- statement:
--   Under the standing assumptions ($n \ge 2$, $R > 0$, $\gamma \ge 0$, all $c_k > 0$, all $n$ miners active), let $g$ be the aggregate equilibrium hash rate, $f_i = h^*_i$ the equilibrium hash rate of miner $i$, and $\Delta_{i,2} = (\partial f_i/\partial g)(\partial g/\partial c_i)$ the indirect sensitivity. Then
--   $$c_i + \gamma f_i = \frac Rg\Big(1 - \frac{f_i}{g}\Big),$$
--   and
--   $$\Delta_{i,2} > 0 \iff c_i + \gamma f_i > \frac12\,\frac Rg \iff \frac{f_i}{g} < \frac12 .$$
--
--   The first identity is the first-order condition of an active miner (Proposition 4.2, posed in mission 1 of this series) written for the closed form; the equivalence is the sign criterion (4.5): the indirect sensitivity is positive exactly for miners with hash rate share below one half.
--
--   **Formalization Note.** $\Delta_{i,2}$ is defined by derivatives (`PoWMining.CostStatics.Setting`). Miner indices are 0-based.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 40, proof of Propositions 4.6 and 4.8 (sign of Δ_{i,2})

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting

namespace PoWMining.CostStatics

theorem sign_Delta2 {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    c i + γ * hstar c γ R i = R / gH c γ R * (1 - hstar c γ R i / gH c γ R) ∧
    (0 < Delta2 c γ R i ↔ 1 / 2 * (R / gH c γ R) < c i + γ * hstar c γ R i) ∧
    (1 / 2 * (R / gH c γ R) < c i + γ * hstar c γ R i ↔ hstar c γ R i / gH c γ R < 1 / 2) := by sorry

end PoWMining.CostStatics
