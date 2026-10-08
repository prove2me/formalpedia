-- Prove2me | Theorems.Thm_VeinottNoDiscount_Overtake_theorem_4
-- name    : VeinottNoDiscount.Overtake.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:46.91031+00:00
-- url     : https://prove2.me/theorems/1cf3c555-f456-4e10-ab54-5094dff38510
-- title:
--   Theorem 4 (Blackwell) — F″ is the nonempty set of f for which f^∞ is 1-optimal
-- statement:
--   In the finite decision model, let $F''$ be the set of decision rules that maximize the gain $x(f)$ and then, among those, the bias $y(f)$. A policy $\pi^*$ is **1-optimal** if
--   $$\lim_{\beta\nearrow1}\bigl[V_\beta(\pi^*)-U(\beta)\bigr]=0,$$
--   where $U(\beta)=V_\beta(\pi(\beta))$ is the discounted return of a $\beta$-optimal policy $\pi(\beta)$. Then $F''$ is nonempty, and for every $f\in F$,
--   $$f\in F''\iff f^\infty\text{ is 1-optimal}.$$
--
--   This links the lexicographic gain–bias criterion to discounting near $\beta=1$; it is what makes the stationary 1-optimal policies computable from $x$ and $y$ alone.
--
--   **Formalization Note** 1-optimality is the published `IsNearlyOptimal` (Blackwell's "nearly optimal", Veinott's footnote 2), stated without $U(\beta)$: for every $\varepsilon>0$ and every $\beta<1$ close enough to $1$, $V_\beta(\pi')\le V_\beta(f^\infty)+\varepsilon$ coordinatewise for every policy $\pi'$. This is equivalent to Veinott's definition because a $\beta$-optimal policy exists for every $\beta\in[0,1)$. The comparison class is all (deterministic, possibly nonstationary) policies.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1286, Theorem 4

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

/-- **Theorem 4 (Blackwell).** `F″` is the (nonempty) set of all `f ε F` for which `f^∞` is
1-optimal.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1286, Theorem 4.

**Formalization Note.** 1-optimal (p. 1285: `lim_{β↗1}[V_β(π*) − U(β)] = 0` with `U(β)` the
value of a β-optimal policy) is the published `IsNearlyOptimal` (Veinott's footnote 2:
Blackwell's "nearly optimal"), encoded without `U` and comparing against every policy, not only
stationary ones. `F″` is `Fdprime M`. -/
theorem theorem_4 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act) :
    (VeinottNoDiscount.Improve.Fdprime M).Nonempty ∧
      ∀ f : St → Act, f ∈ VeinottNoDiscount.Improve.Fdprime M ↔ M.IsNearlyOptimal (Policy.stationary f) := by sorry

end VeinottNoDiscount.Overtake
