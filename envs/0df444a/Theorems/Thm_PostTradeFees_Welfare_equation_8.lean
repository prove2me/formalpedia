-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_equation_8
-- name    : PostTradeFees.Welfare.equation_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:12.367715+00:00
-- url     : https://prove2.me/theorems/afc99018-8bc3-4ae1-8cca-c4e3f60ae249
-- title:
--   Equation (8), pp. 15–16 (PDF 16–17) — welfare turning point c₂
-- statement:
--   Let $N>1$, $V_h>V_l\ge0$, and $c>0$. Compute welfare from any stationary distributions of the "all" and "own" trading chains. The two welfare levels are equal exactly at
--
--   $$
--   c=c_2=\frac{N(V_h-V_l)}{2N+1}.
--   $$
--
--   Welfare under "all" is at least welfare under "own" exactly when $c\le c_2$. This identifies the socially preferred strategy independently of the fee structure that traders face.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), pp. 15–16 (PDF 16–17), Equation (8) and preceding welfare comparison

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Equation (8): the two strategies have equal welfare exactly at c₂. -/
theorem equation_8 (P : Params) (hS : P.Standing)
    (φa φo : Fin 3 → ℝ)
    (hφa : MarkovChain.IsStationary (chainAll P.N) φa)
    (hφo : MarkovChain.IsStationary (chainOwn P.N) φo) :
    (welfare P φa = welfare P φo ↔ P.c = c2 P) ∧
    (welfare P φo ≤ welfare P φa ↔ P.c ≤ c2 P) := by sorry

end PostTradeFees.Welfare
