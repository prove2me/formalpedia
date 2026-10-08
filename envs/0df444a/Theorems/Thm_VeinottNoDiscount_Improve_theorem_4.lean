-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_theorem_4
-- name    : VeinottNoDiscount.Improve.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:43.00139+00:00
-- url     : https://prove2.me/theorems/9c757b31-fb1f-4205-a05b-6f9543d15c88
-- title:
--   Theorem 4 (Blackwell) — F″ is the nonempty set of f for which f^∞ is 1-optimal
-- statement:
--   In the finite decision model, let $F''$ be the set of decision rules $f$ of maximal gain $x(f)$ that, among those, have maximal bias $y(f)$. A policy $\pi^*$ is **1-optimal** if
--   $$\lim_{\beta\nearrow1}\big[V_\beta(\pi^*)-U(\beta)\big]=0,$$
--   where $U(\beta)$ is the value of a $\beta$-optimal policy. Then $F''$ is nonempty, and for every $f\in F$,
--   $$f\in F''\iff f^\infty\text{ is 1-optimal}.$$
--
--   The theorem reduces the search for a 1-optimal stationary policy to lexicographic maximization of gain and then bias.
--
--   **Formalization Note** 1-optimality is the published Blackwell notion "nearly optimal", encoded without $U$: for every $\varepsilon>0$ and all $\beta<1$ close enough to $1$, $V_\beta(\pi)\le V_\beta(\pi^*)+\varepsilon$ coordinatewise for every policy $\pi$ (not only stationary ones).
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1286, Theorem 4

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Theorem 4 (Blackwell).** `F″` is the (nonempty) set of all `f ε F` for which `f^∞` is
1-optimal.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1286, Theorem 4.

**Formalization Note.** 1-optimal (p. 1285: `lim_{β↗1}[V_β(π*) − U(β)] = 0` with `U(β)` the
value of a β-optimal policy) is the published `IsNearlyOptimal` (Veinott's footnote 2: Blackwell's
"nearly optimal"), encoded without `U` and comparing against every policy, not only stationary
ones. `F″` is `Fdprime M`. -/
theorem theorem_4 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act) :
    (Fdprime M).Nonempty ∧
      ∀ f : St → Act, f ∈ Fdprime M ↔ M.IsNearlyOptimal (Policy.stationary f) := by sorry

end VeinottNoDiscount.Improve
