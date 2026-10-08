-- Prove2me | Theorems.Thm_QualityEncroach_Differ_reduced_profit_high
-- name    : QualityEncroach.Differ.reduced_profit_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:48.741974+00:00
-- url     : https://prove2.me/theorems/8d9f63a2-8d64-44cc-8a2e-7a2738f7f3fd
-- title:
--   Proof of Lemma 1(i), p. 29 — max over w of Π_M(w,t,u) is attained at w(t,u) with value Π_M(t,u) (t ≤ 1)
-- statement:
--   Fix $k>0$, $c\ge0$, $u>0$ and $0<t\le1$. Evaluate the manufacturer's profit at the subgame quantities $q_R(w,u,t)$, $q_M(w,u,t)$ of (7), as a function of the wholesale price $w$:
--
--   $$
--   \Pi_M(w,t,u)=\bigl(w-k(tu)^2\bigr)q_R(w,u,t)+\bigl(u(1-q_M(w,u,t)-t\,q_R(w,u,t))-c-ku^2\bigr)q_M(w,u,t).
--   $$
--
--   This function of $w$ has the unique maximizer
--
--   $$
--   w(t,u)=\frac{tu}{2}+\frac{kt^2(7-4t)u^2}{2(8-5t)}-\frac{ct^2}{2(8-5t)},
--   $$
--
--   and its maximum value is
--
--   $$
--   \Pi_M(t,u)=\frac{4k^2u^3t^3-(8k^2u^3+8kcu)t^2-(k^2u^3+2kcu+\frac{c^2}{u})t+8k^2u^3+16kcu+\frac{8c^2}{u}}{4(8-5t)}-\frac{2ku^2-u+2c}{4}.
--   $$
--
--   This links the reduced profit $\Pi_M(t,u)$, studied in Lemma 1(i), to the game.
--
--   **Formalization Note.** The statement is about the closed forms: the nonnegativity of the quantities is not imposed, exactly as in the page's computation "$\max_w\Pi_M(w,t,u)$". At $t=1$, (7) coincides with the uniform-quality quantities (3).
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 29, proof of Lemma 1(i)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Definitions.Def_QualityEncroach_Differ_Reduced

namespace QualityEncroach.Differ

theorem reduced_profit_high (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (t u : ℝ) (hu : 0 < u)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    mfrPayoff k c ⟨wH k c t u, u, t, qR7 k c (wH k c t u) u t, qM7 k c (wH k c t u) u t⟩ =
        PiH k c t u ∧
    ∀ w : ℝ, w ≠ wH k c t u →
      mfrPayoff k c ⟨w, u, t, qR7 k c w u t, qM7 k c w u t⟩ < PiH k c t u := by sorry

end QualityEncroach.Differ
