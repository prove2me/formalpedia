-- Prove2me | Theorems.Thm_StrategicQR_Game_myopic_qr_newsvendor
-- name    : StrategicQR.Game.myopic_qr_newsvendor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:43.476346+00:00
-- url     : https://prove2.me/theorems/548475c8-180c-436d-8732-98efb9ad5f5a
-- title:
--   Proof of Theorem 2 (iii), p. 21 — $F(q_r^m)=(c_2-c_1)/(c_2-v_B)$, and $v^*(q_r^m)=\bar v$ iff (6)
-- statement:
--   Let $v_B<c_1\le c_2\le p$ and let $\pi_r^m$ be the profit with quick response when all consumers are myopic ($\alpha=0$). Then:
--
--   1. $\pi_r^m$ has a maximizer on $[0,\infty)$;
--   2. $q\ge0$ maximizes $\pi_r^m$ if and only if $F(q)=\dfrac{c_2-c_1}{c_2-v_B}$;
--   3. for every such $q$ and every $0<\alpha\le1$, the threshold $\bar v$ is a consumer best response to $q$ (all strategic consumers buy in the first period) if and only if
--   $$\frac{v_M-p}{\bar v-v_B}\ge\frac{c_2-c_1}{c_2-v_B}.\qquad(6)$$
--
--   Part 3 is the paper's computation "$v_M-p\ge F(q_r^m)(\bar v-v_B)$, and since $q_r^m=F^{-1}((c_2-c_1)/(c_2-v_B))$ this reduces to (6)".
--
--   **Formalization Note** With $\alpha=0$ the belief has no effect; $\pi_r^m$ is evaluated at $\hat v=\bar v$. Part 3 holds for any $q$ with $F(q)=(c_2-c_1)/(c_2-v_B)$.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 21, proof of Theorem 2 (iii), unnumbered display; p. 20, condition (6)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- The myopic quick-response benchmark (proof of Theorem 2 (iii), p. 21). For
`vB < c₁ ≤ c₂ ≤ p`, the myopic profit with quick response `π_r^m` (`α = 0`) has a maximizer on
`[0, ∞)`, `q ≥ 0` is a maximizer iff `F(q) = (c₂ - c₁)/(c₂ - vB)`, and for such `q` and any
`0 < α ≤ 1`, `v̄` is a consumer best response to `q` (`v*(q_r^m) = v̄`) iff (6),
`(vM - p)/(v̄ - vB) ≥ (c₂ - c₁)/(c₂ - vB)`, holds. -/
theorem myopic_qr_newsvendor (M : Model) {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc₁ : M.vB < c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂p : c₂ ≤ M.p) :
    (∃ q ∈ Set.Ici (0 : ℝ), IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) q) ∧
    (∀ q ∈ Set.Ici (0 : ℝ), (IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) q ↔
      demandCdf M.f q = (c₂ - c₁) / (c₂ - M.vB))) ∧
    (∀ q, demandCdf M.f q = (c₂ - c₁) / (c₂ - M.vB) →
      (IsConsumerBR M α q M.vhi ↔ (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))) := by sorry

end StrategicQR.Game
