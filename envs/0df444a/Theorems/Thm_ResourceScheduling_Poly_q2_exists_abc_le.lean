-- Prove2me | Theorems.Thm_ResourceScheduling_Poly_q2_exists_abc_le
-- name    : ResourceScheduling.Poly.q2_exists_abc_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:32:43.413578+00:00
-- url     : https://prove2.me/theorems/1e1b3ad0-c18c-4483-8b62-793c44e77634
-- title:
--   Proof of Theorem 5 — every feasible schedule can be transformed into an (a)–(c) schedule at least as good
-- statement:
--   Consider two uniform machines $M_1,M_2$ with speeds $q_1\ge q_2>0$, one resource of positive integer size $s_1$, $n$ unit-time jobs with requirements $r_{1j}$, and no precedence constraints. For every feasible schedule $\sigma$ there is a feasible schedule $\sigma'$ that satisfies properties (a), (b) and (c) of the proof of Theorem 5 and has
--   $$C_{\max}(\sigma')\le C_{\max}(\sigma).$$
--
--   In the paper's words: "The correctness of the algorithm will now be proved by showing that any feasible schedule can be transformed into a schedule that is at least as good and satisfies properties (a), (b) and (c)." It reduces the optimality of the algorithm to a comparison among (a)–(c) schedules only.
--
--   **Formalization Note** Start times are real and the resource constraint is checked at every real time; the transformed schedule is again nonpreemptive.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 16–17, proof of Theorem 5 ("any feasible schedule can be transformed into a schedule that is at least as good")

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties

namespace ResourceScheduling.Poly

/-- Proof of Theorem 5 (p. 16), the exchange argument: for `Q2 | res1··, p_j = 1 | C_max` with
`q_1 ≥ q_2`, every feasible schedule can be transformed into a feasible schedule that is at least
as good and satisfies properties (a), (b) and (c). -/
theorem q2_exists_abc_le (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (hprec : I.NoPrecedence) (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm))
    (σ : Schedule I) (hσ : σ.Feasible) :
    ∃ σ' : Schedule I, σ'.Feasible ∧ σ'.SatisfiesABC hm hl ∧ σ'.makespan ≤ σ.makespan := by sorry

end ResourceScheduling.Poly
