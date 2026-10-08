-- Prove2me | Theorems.Thm_QualityEncroach_Uniform_wholesale_and_profits_given_u
-- name    : QualityEncroach.Uniform.wholesale_and_profits_given_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:20.676214+00:00
-- url     : https://prove2.me/theorems/1be0e192-ad4a-468e-bba7-5f235e5e715a
-- title:
--   §4.1, p. 10, (4)–(5) — w^U(u) = ku²/2 + u/2 − c/6, the quantities at w^U(u), and Π^U_M(u), Π^U_R(u) = 2c²/(9u)
-- statement:
--   Let $k>0$, $c\ge 0$ and a quality $u>0$ be given, and let the quantities follow the subgame solution (3), $q^U_R(w,u)$ and $q^U_M(w,u)$. Then:
--
--   1. the manufacturer's profit
--   $$(w-ku^2)q^U_R(w,u)+\big(u-uq^U_M(w,u)-uq^U_R(w,u)-c-ku^2\big)q^U_M(w,u)$$
--   has the unique maximizer over $w\in\mathbb R$
--   $$w^U(u)=\frac{ku^2}{2}+\frac u2-\frac c6;$$
--   2. the corresponding quantities are $q^U_R(w^U(u),u)=\tfrac{2c}{3u}$ and $q^U_M(w^U(u),u)=-\tfrac{ku}{2}-\tfrac{5c}{6u}+\tfrac12$;
--   3. the profits are
--   $$\Pi^U_M(u)=\frac{k^2u^3}{4}+\frac{kcu}{2}+\frac{7c^2}{12u}-\frac{ku^2}{2}+\frac u4-\frac c2,\qquad \Pi^U_R(u)=\frac{2c^2}{9u}.$$
--
--   These are equations (4) and (5) of the paper.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 10, §4.1, equations (4)–(5) and the display between them

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

namespace QualityEncroach.Uniform

/-- §4.1, p. 10, (4)–(5): for a given quality `u > 0`, with the subgame quantities
`q^U_R(w, u)`, `q^U_M(w, u)` of (3), the manufacturer's profit is uniquely maximized over `w` at
`w^U(u) = ku²/2 + u/2 − c/6`; there `q^U_R = 2c/(3u)` and `q^U_M = −ku/2 − 5c/(6u) + 1/2`, and
the two profits are `Π^U_M(u)` and `Π^U_R(u) = 2c²/(9u)`. -/
theorem wholesale_and_profits_given_u (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (u : ℝ) (hu : 0 < u) :
    (∀ w : ℝ, w ≠ wU k c u →
        mfrPayoff k c ⟨w, u, qUR k c w u, qUM k c w u⟩ <
          mfrPayoff k c ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩) ∧
    qUR k c (wU k c u) u = 2 * c / (3 * u) ∧
    qUM k c (wU k c u) u = -(k * u) / 2 - 5 * c / (6 * u) + 1 / 2 ∧
    mfrPayoff k c ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩ = PiUM k c u ∧
    retailerPayoff ⟨wU k c u, u, qUR k c (wU k c u) u, qUM k c (wU k c u) u⟩ = PiUR c u := by sorry

end QualityEncroach.Uniform
