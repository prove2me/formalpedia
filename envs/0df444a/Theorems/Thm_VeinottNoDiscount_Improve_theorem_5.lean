-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_theorem_5
-- name    : VeinottNoDiscount.Improve.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:29.281811+00:00
-- url     : https://prove2.me/theorems/09d9c83a-ed73-4ab5-9b5a-aa8ef028e766
-- title:
--   Theorem 5 (Blackwell) — G(f) empty ⇒ f ∈ F′; g ∈ G(f) ⇒ V_β(g^∞) > V_β(f^∞) for β near 1
-- statement:
--   Let $f\in F$, and let $G(f)$ be Veinott's set of improving decision rules (defined from the inequalities (i), (ii) on gain and bias). Then:
--
--   1. if $G(f)$ is empty, then $f\in F'$, i.e. $x(f)\ge x(g)$ for every $g\in F$;
--   2. if $g\in G(f)$, then there is $\beta_0<1$ such that
--   $$V_\beta(g^\infty)>V_\beta(f^\infty)\qquad\text{for all }\beta_0<\beta<1,$$
--   where $u>v$ means $u\ge v$ coordinatewise and $u\ne v$.
--
--   This is Howard's policy improvement method for maximal average return per unit time.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1287, Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Theorem 5 (Blackwell).** Suppose `f ε F`.
(a) If `G(f)` is empty, then `f ε F′`.
(b) If `g ε G(f)`, then `V_β(g^∞) > V_β(f^∞)` for all `β (< 1)` sufficiently near 1.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1287, Theorem 5.

**Formalization Note.** `G(f)` is Veinott's set `GSet M f` (four clauses, p. 1287), not
Blackwell's per-state `G(s, f)`. `>` is `VecGt` (`≧` and `≠`). "For all β (< 1) sufficiently
near 1" is: there is `β₀ < 1` with the conclusion for every `β ∈ (β₀, 1)`. -/
theorem theorem_5 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (GSet M f = ∅ → f ∈ Fprime M) ∧
      ∀ g ∈ GSet M f, ∃ β₀ < (1 : ℝ), ∀ β : ℝ, β₀ < β → β < 1 →
        VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f)) := by sorry

end VeinottNoDiscount.Improve
