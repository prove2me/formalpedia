-- Prove2me | Theorems.Thm_SantosHirsch_Counter_theorem_3_1
-- name    : SantosHirsch.Counter.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:54:56.396079+00:00
-- url     : https://prove2.me/theorems/77f1f2a5-2666-45a8-9fa6-52566cd44f87
-- title:
--   Theorem 3.1 (polar form) — the apices ±e₅ of the polar spindle are at graph distance exactly six
-- statement:
--   Let $Q^\Delta\subset\mathbb R^5$ be the polar of Santos's prismatoid, with apices $e_5$ and $-e_5$. In the vertex-edge graph of $Q^\Delta$ there is a walk of six steps from $e_5$ to $-e_5$, and there is none with fewer steps:
--   $$\operatorname{dist}_{G(Q^\Delta)}(e_5,-e_5)=6.$$
--
--   This is the length of the spindle in Theorem 1.6; since $6>5$ it is the input that makes Theorem 1.5 produce a non-Hirsch polytope.
--
--   **Formalization Note** Polar form: the width of the prismatoid $Q$ (dual graph distance between $Q^+$ and $Q^-$) is the graph distance between the apices $\pm e_5$ of the polar spindle. A walk of $L$ steps allows stationary steps (platform `Hirsch.Reach`), so "exactly six" is stated as a 6-step walk exists and no walk of $k<6$ steps exists.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 10, Theorem 3.1

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Theorem 3.1 (p. 10), polar form: in the vertex-edge graph of the polar spindle the
apices `e₅` and `−e₅` are at distance exactly six. -/
theorem theorem_3_1 :
    Hirsch.Reach santosSpindle 6 apexPlus apexMinus ∧
    ∀ k < 6, ¬ Hirsch.Reach santosSpindle k apexPlus apexMinus := by sorry

end SantosHirsch.Counter
