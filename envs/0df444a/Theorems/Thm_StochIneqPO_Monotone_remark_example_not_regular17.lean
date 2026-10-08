-- Prove2me | Theorems.Thm_StochIneqPO_Monotone_remark_example_not_regular17
-- name    : StochIneqPO.Monotone.remark_example_not_regular17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:28:29.392995+00:00
-- url     : https://prove2.me/theorems/c0690592-7b37-436d-942b-47ca7f2d2341
-- title:
--   Remarks after Theorem 6, p. 909 — a Polish space with a closed linear order in which (17) fails
-- statement:
--   Let $E=\{x_n=(1-\tfrac1n,0)\}_{n\ge1}\cup\{z=(1,0)\}\cup\{y_n=(n,1)\}_{n\ge1}\subseteq\mathbb R^2$ with the metric induced by $\mathbb R^2$ and the linear ordering in which $x_n<y_n<x_{n+1}<z$ for all $n$. Then:
--
--   1. $E$ is a closed subset of $\mathbb R^2$, hence complete; it is separable (second countable); so $E$ is a Polish space;
--   2. the ordering is closed: $\{(a,b)\in E\times E : a\le b\}$ is closed in $E\times E$;
--   3. the ordering satisfies
--   $$
--   x_n<y_n<x_{n+1}<z\qquad (n\ge1);
--   $$
--   4. $E$ does not satisfy condition (17).
--
--   The example shows that the second part of Theorem 6 is not vacuous: there are Polish spaces with a closed partial ordering in which some nondecreasing sequence of random elements converges in probability but not almost surely.
--
--   **Formalization Note** The space is `RemarkSpace` (the subtype with the linear order pulled back along an injective rank; see that definition). Closedness of $E$ is stated in $\mathbb R\times\mathbb R$ with Mathlib's product topology, which is the topology of $\mathbb R^2$. Completeness, second countability and closedness of the order are part of the claim and are not assumed as instances. Item 3 records that the order is the paper's. The Lean index $k$ is the paper's $n=k+1$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Remarks after Theorem 6, p. 909 (PDF p. 11)

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_RemarkSpace

namespace StochIneqPO.Monotone

theorem remark_example_not_regular17 :
    IsClosed remarkSet ∧ CompleteSpace RemarkSpace ∧
      SecondCountableTopology RemarkSpace ∧ OrderClosedTopology RemarkSpace ∧
      (∀ k : ℕ, RemarkSpace.x k < RemarkSpace.y k ∧ RemarkSpace.y k < RemarkSpace.x (k + 1) ∧
        RemarkSpace.x (k + 1) < RemarkSpace.z) ∧
      ¬ Regular17 RemarkSpace := by sorry

end StochIneqPO.Monotone
