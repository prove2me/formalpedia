-- Prove2me | Theorems.Thm_SLPricing_Resp_eq_8
-- name    : SLPricing.Resp.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:53.891181+00:00
-- url     : https://prove2.me/theorems/04a445e7-b0e4-4d3d-92db-312e2c2b2570
-- title:
--   (8), p. 22 (corrected) — the responsive expected profit $\pi_r(p_1)$ in terms of the threshold $\zeta$
-- statement:
--   Consider responsive pricing in the mission's model. Let $(B,s)$ be an equilibrium after a first-period price $p_1$ whose set of first-period buyers $B$ equals $[\zeta,1]$ up to a null set, for some $\zeta\in[0,1]$, and let $f(\cdot;\zeta)$ be the pre-posterior law of $q_u$ for a mass $1-\zeta$ of reviews. Then the firm's expected profit is
--   $$\pi_r(p_1)=(p_1-c)(1-\zeta)+\int_{c-\zeta}^{c+\zeta}\Big(\frac{q_u+\zeta-c}{2}\Big)^2 f(q_u;\zeta)\,dq_u+\int_{c+\zeta}^{\infty}\zeta\,(q_u-c)\,f(q_u;\zeta)\,dq_u .$$
--   The first term is first-period profit; the integrals are the expected optimal second-period profit, which is $0$ when $q_u\le c-\zeta$ (the firm exits), $\big(\frac{q_u+\zeta-c}{2}\big)^2$ for intermediate $q_u$, and $\zeta(q_u-c)$ when the firm clears the market.
--
--   This is the objective the firm maximizes over $p_1$ under responsive pricing.
--
--   **Formalization Note** The page prints the last integrand as $\zeta q_u f(q_u;\zeta)$. The proof of Lemma 3 (p. 31) gives the optimal second-period profit $(q_u-c)\bar x$ when $q_u>c+\bar x$, so the integrand is $\zeta(q_u-c)$; the statement uses the corrected form. The expression holds for every equilibrium with threshold $\zeta$, whatever price the rule $s$ selects in the exit region (every optimal price sells nothing there).
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), equation (8), p. 22; proof of Lemma 3, p. 31

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- (8), p. 22, with the last integrand corrected to `ζ(q_u − c)` as the proof of Lemma 3
(p. 31) gives it: in every equilibrium after a first-period price `p₁` whose first-period buyers
are the types `[ζ, 1]` (up to a null set), `ζ ∈ [0, 1]`, the firm's expected profit is
`(p₁ − c)(1 − ζ) + E[π₂*(q_u)]`, where `q_u` has the pre-posterior law for a mass `1 − ζ` of
reviews and `π₂*` is `0` for `q_u ≤ c − ζ`, `((q_u + ζ − c)/2)²` for `c − ζ < q_u ≤ c + ζ` and
`ζ(q_u − c)` for `q_u > c + ζ`. -/
theorem eq_8 (P : Params) (hP : P.Standing) (p₁ ζ : ℝ) (hζ : ζ ∈ Icc (0 : ℝ) 1)
    (B : Set ℝ) (s : ℝ → ℝ) (heq : IsRespEq P p₁ B s) (hB : B =ᵐ[volume] Icc ζ 1) :
    respProfit P p₁ B s =
      (p₁ - P.c) * (1 - ζ) +
        ∫ q, (if q ≤ P.c - ζ then 0
              else if q ≤ P.c + ζ then ((q + ζ - P.c) / 2) ^ 2
              else ζ * (q - P.c)) ∂(prePost P (1 - ζ)) := by sorry

end SLPricing.Resp
