-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_quantity_subgame
-- name    : QualityEncroach.Uniform.quantity_subgame
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:29.596006+00:00
-- url     : https://prove2.me/theorems/e9895316-14f2-4ea3-b972-31806a18d1fe
-- title:
--   §4.1, p. 10, (3) — the quantity subgame given (w, u): q^U_R(w,u) and q^U_M(w,u)
-- statement:
--   Let $k>0$, $c\ge0$, a wholesale price $w$ and a quality $u>0$ be given, and write $\bar q=1-\tfrac cu-ku$.
--
--   1. For every order $0\le q_R\le\bar q$, the retailer's profit when the manufacturer replies with $q^U_M(q_R,w,u)$ equals
--   $$-\tfrac12 u q_R^2+\big(\tfrac12u+\tfrac12ku^2+\tfrac c2-w\big)q_R .$$
--   2. This quadratic in $q_R$ is maximized over all reals at
--   $$q^U_R(w,u)=\frac12-\frac wu+\frac{ku}{2}+\frac{c}{2u}.$$
--   3. If $0\le q^U_R(w,u)\le\bar q$, the manufacturer's reply to it is
--   $$q^U_M(q^U_R(w,u),w,u)=q^U_M(w,u)=\frac14+\frac{w}{2u}-\frac{3ku}{4}-\frac{3c}{4u}.$$
--   In this region, $q^U_R(w,u)$ maximizes the retailer's payoff over every nonnegative order, including orders above $\bar q$ for which the manufacturer sells nothing directly.
--
--   Together these give equation (3), the solution of the quantity competition subgame for given $w$ and $u$.
--
--   **Formalization Note.** The paper derives (3) "assuming $q_R\le 1-c/u-ku$"; that assumption is a hypothesis of parts 1 and 3, not dropped.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 10, §4.1, equation (3) and the two displays before it

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- §4.1, p. 10, (3): the quantity subgame for given `(w, u)`, `u > 0`.
(a) For `0 ≤ q_R ≤ 1 − c/u − ku`, the retailer's profit when the manufacturer replies with
`q^U_M(q_R, w, u)` is `−½ u q_R² + (½u + ½ku² + c/2 − w) q_R`.
(b) This quadratic is maximized at `q^U_R(w, u) = 1/2 − w/u + ku/2 + c/(2u)`.
(c) If `0 ≤ q^U_R(w, u) ≤ 1 − c/u − ku`, the manufacturer's reply to it is
`q^U_M(w, u) = 1/4 + w/(2u) − 3ku/4 − 3c/(4u)`, and this retailer order is
optimal among all nonnegative orders, including those outside the region of the quadratic. -/
theorem quantity_subgame (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w u : ℝ) (hu : 0 < u) :
    (∀ qR : ℝ, 0 ≤ qR → qR ≤ 1 - c / u - k * u →
        retailerPayoff ⟨w, u, qR, qUM_br k c qR w u⟩ =
          -(1 / 2) * u * qR ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qR) ∧
    (∀ q : ℝ, -(1 / 2) * u * q ^ 2 + ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * q ≤
        -(1 / 2) * u * qUR k c w u ^ 2 +
          ((1 / 2) * u + (1 / 2) * k * u ^ 2 + c / 2 - w) * qUR k c w u) ∧
    (0 ≤ qUR k c w u → qUR k c w u ≤ 1 - c / u - k * u →
        qUM_br k c (qUR k c w u) w u = qUM k c w u ∧
        ∀ qR : ℝ, 0 ≤ qR →
          retailerPayoff ⟨w, u, qR, qUM_br k c qR w u⟩ ≤
            retailerPayoff ⟨w, u, qUR k c w u, qUM k c w u⟩) := by sorry

end QualityEncroach.Uniform
