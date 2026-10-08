-- Prove2me | Theorems.Thm_StochIneqPO_Comparison_prop2_le_of_marginals_le
-- name    : StochIneqPO.Comparison.prop2_le_of_marginals_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:20.120582+00:00
-- url     : https://prove2.me/theorems/3b1f9135-5d27-44e0-a411-de13aa6229d8
-- title:
--   Proposition 2 — on $E^\infty$, $P \prec Q$ follows from $P^{(i)} \prec Q^{(i)}$ for all finite-dimensional marginals
-- statement:
--   Let $E_1, E_2, \dots$ be partially ordered Polish spaces and let $F = E^\infty = \prod_{i=1}^\infty E_i$, with the product topology and the coordinatewise order. Let $P, Q$ be probability measures on $F$, and let $P^{(i)}$, $Q^{(i)}$ be their marginals on the first $i$ coordinates, probability measures on $E^{i} = E_1 \times \cdots \times E_i$. If
--   $$P^{(i)} \prec Q^{(i)}, \qquad i = 1, 2, \dots, \tag{3}$$
--   then $P \prec Q$.
--
--   The stochastic order on the sequence space is thus determined by the finite-dimensional marginals; this is the step from Proposition 1 to Theorem 2.
--
--   **Formalization Note** The marginal on the first $i$ coordinates is the image of $P$ under restriction to `Iic (i - 1)` (`Preorder.frestrictLe`); with 0-based indices, "for all $i \ge 1$" is "for all `i : ℕ`". The standing assumption of Sec. 1 makes each $E_i$ a *partially ordered* Polish space, although the statement says "Polish spaces".
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Proposition 2, eq. (3), p. 902 (PDF p. 4)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory Finset

theorem prop2_le_of_marginals_le {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)]
    [∀ n, PolishSpace (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
    [∀ n, PartialOrder (E n)] [∀ n, OrderClosedTopology (E n)]
    (P Q : Measure (Π n, E n)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ i : ℕ, StochLE (P.map (Preorder.frestrictLe i)) (Q.map (Preorder.frestrictLe i))) :
    StochLE P Q := by sorry

end StochIneqPO.Comparison
