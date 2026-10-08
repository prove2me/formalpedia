-- Prove2me | Theorems.Thm_SantosHirsch_Counter_santos_spindle
-- name    : SantosHirsch.Counter.santos_spindle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:54:05.789406+00:00
-- url     : https://prove2.me/theorems/665ff36e-3ef7-4e74-bc6f-9f96077446c9
-- title:
--   §3, first bullet (polar form) — the polar of Santos's prismatoid is a 48-facet 5-spindle with apices ±e₅
-- statement:
--   Let $r_1,\dots,r_{48}\in\mathbb R^5$ be the rows $1^+,\dots,24^+,1^-,\dots,24^-$ of Table 1, and let
--   $$Q^\Delta=\{x\in\mathbb R^5:\ \langle r_i,x\rangle\le 1,\ i=1,\dots,48\}.$$
--   Then:
--
--   1. $Q^\Delta$ is bounded;
--   2. its 48 inequalities form a facet presentation: $Q^\Delta$ has nonempty interior and none of the inequalities is redundant;
--   3. $Q^\Delta$ is a spindle with apices $e_5=(0,0,0,0,1)$ and $-e_5$: both are vertices, and every inequality is tight at exactly one of them;
--   4. the inequalities tight at $e_5$ are exactly those of $1^+,\dots,24^+$, and the ones tight at $-e_5$ are exactly those of $1^-,\dots,24^-$.
--
--   This is the polar form of Santos's observation that the vertices $1^+,\dots,24^+$ and $1^-,\dots,24^-$ of the prismatoid $Q$ span the two facets $Q^+\subset\{x_5=1\}$ and $Q^-\subset\{x_5=-1\}$, so that $Q$ is a prismatoid with the 48 rows of Table 1 as vertices. It supplies the witness for Theorem 1.6.
--
--   **Formalization Note** In the polar ($0\in\operatorname{int}Q$): the 48 vertices of $Q$ are the 48 irredundant rows; boundedness of $Q^\Delta$ is $0\in\operatorname{int}Q$; the base facets $Q^\pm$ are the vertices $\pm e_5$; "every vertex of $Q$ lies in exactly one of $Q^+,Q^-$" is the spindle condition. The polar translation is licensed by Santos, p. 8 ("The following class of polytopes are the polars of the spindles").
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 11, §3, first bullet, and the caption of Table 1

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- §3, first bullet (p. 11), polar form: the polar of Santos's prismatoid is a bounded
5-polytope whose 48 rows are irredundant facet inequalities, and it is a spindle with apices
`e₅` and `−e₅`; the rows tight at `e₅` are exactly `1⁺ … 24⁺`, those tight at `−e₅` exactly
`1⁻ … 24⁻`. -/
theorem santos_spindle :
    Bornology.IsBounded santosSpindle ∧
    IsFacetPresentation santosRows (fun _ => 1) ∧
    IsSpindle santosRows (fun _ => 1) apexPlus apexMinus ∧
    (∀ i : Fin 48, ⟪santosRows i, apexPlus⟫ = 1 ↔ (i : ℕ) < 24) ∧
    (∀ i : Fin 48, ⟪santosRows i, apexMinus⟫ = 1 ↔ 24 ≤ (i : ℕ)) := by sorry

end SantosHirsch.Counter
