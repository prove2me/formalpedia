-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_proposition_1
-- name    : RetailPrivacy.SingleFirm.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:32.986015+00:00
-- url     : https://prove2.me/theorems/0060644c-326d-452d-8b7b-f8be430a50ea
-- title:
--   Proposition 1, p. 14 — the ℝ-mode equilibrium: ℓ* = 1 and (r*, p*, 𝒯₁(p*)) on v ≤ 2ℳ/𝒵² and v > 2ℳ/𝒵²
-- statement:
--   Let $c>0$, $\delta\in(0,1)$, $v>0$, with $\mathcal Z = 2c+\delta$ and $\mathcal M = 4c^2(1-\delta)+c\delta(4-3\delta)+\delta^2$. Under the $\mathbb R$ mode the single-firm game has a subgame-perfect equilibrium, and in every subgame-perfect equilibrium the firm collects data ($\ell^*=1$), and its on-path monetization intensity $r^*$, price $p^*$ and sales quantity $\mathcal T_1(p^*)$ are
--   $$(r^*,p^*,\mathcal T_1(p^*)) = \begin{cases} \left(\dfrac{v\delta\mathcal Z}{2\mathcal M},\ \dfrac v2-\dfrac{vc\delta^2}{2\mathcal M},\ \dfrac{v\mathcal Z^2}{2\mathcal M}\right) & \text{if } v\le \dfrac{2\mathcal M}{\mathcal Z^2},\\[3mm] \left(\dfrac{\delta}{\mathcal Z},\ v-1+\dfrac{2c\delta}{\mathcal Z},\ 1\right) & \text{if } v> \dfrac{2\mathcal M}{\mathcal Z^2}.\end{cases}$$
--
--   This is the pre-GDPR benchmark against which Theorem 1 measures the GDPR.
--
--   **Formalization Note** The price ranges over all of $\mathbb R$ and the firm's collection decision is compared against the full off-path subgame $\ell = 0$. The hypothesis $v>0$ is not in the paper; it is implicit (at $v \le 0$ nothing is sold).
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 14, Proposition 1; proof pp. ec21–ec22

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem proposition_1 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧
    ∀ P : Profile, IsSPE .R v c δ P →
      P.collect = true ∧
      (v ≤ 2 * Mc c δ / Zc c δ ^ 2 →
        (eqResp P).2 = v * δ * Zc c δ / (2 * Mc c δ) ∧
        eqPrice P = v / 2 - v * c * δ ^ 2 / (2 * Mc c δ) ∧
        demand true v δ (eqPrice P) (eqResp P).2 = v * Zc c δ ^ 2 / (2 * Mc c δ)) ∧
      (2 * Mc c δ / Zc c δ ^ 2 < v →
        (eqResp P).2 = δ / Zc c δ ∧
        eqPrice P = v - 1 + 2 * c * δ / Zc c δ ∧
        demand true v δ (eqPrice P) (eqResp P).2 = 1) := by sorry

end RetailPrivacy.SingleFirm
