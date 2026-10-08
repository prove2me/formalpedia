-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_stage3_best_response
-- name    : QualityEncroach.Uniform.stage3_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:23.600964+00:00
-- url     : https://prove2.me/theorems/3944345d-6c19-4dd9-a9a8-e136f2a119ec
-- title:
--   §4.1, p. 10 — the manufacturer's stage-3 best response q^U_M(q_R,w,u) = (1/2 − q_R/2 − c/(2u) − ku/2)⁺
-- statement:
--   Let $k>0$, $c\ge0$, and consider the last stage of the encroachment game with uniform quality, after the manufacturer has chosen $(w,u)$ with $u>0$ and the retailer has ordered $q_R\ge0$. The manufacturer chooses her direct quantity $q_M\ge0$ to maximize
--   $$(w-ku^2)\,q_R+(u-uq_M-uq_R-c-ku^2)\,q_M .$$
--   The unique maximizer over $q_M\ge 0$ is
--   $$q^U_M(q_R,w,u)=\Big(\frac12-\frac{q_R}{2}-\frac{c}{2u}-\frac{ku}{2}\Big)^+ .$$
--
--   This is the first step of the backward induction of §4.1.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 9–10, §4.1, display at the foot of p. 9 and the first line of p. 10

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- §4.1, p. 10: given `(w, u, q_R)` with `u > 0` and `q_R ≥ 0`, the manufacturer's unique best direct quantity
over `q_M ≥ 0` is `q^U_M(q_R, w, u) = (1/2 − q_R/2 − c/(2u) − ku/2)⁺`. -/
theorem stage3_best_response (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u qR : ℝ)
    (hu : 0 < u) (hqR : 0 ≤ qR) :
    0 ≤ qUM_br k c qR w u ∧
    ∀ qM : ℝ, 0 ≤ qM → qM ≠ qUM_br k c qR w u →
      mfrPayoff k c ⟨w, u, qR, qM⟩ < mfrPayoff k c ⟨w, u, qR, qUM_br k c qR w u⟩ := by sorry

end QualityEncroach.Uniform
