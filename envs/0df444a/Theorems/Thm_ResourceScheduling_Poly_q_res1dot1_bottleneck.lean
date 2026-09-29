-- Prove2me | Theorems.Thm_ResourceScheduling_Poly_q_res1dot1_bottleneck
-- name    : ResourceScheduling.Poly.q_res1dot1_bottleneck
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:33:46.298266+00:00
-- url     : https://prove2.me/theorems/c5212013-de59-49c8-9495-7b86e781ff80
-- title:
--   Proof of Theorem 6 — Q | res1·1, p_j = 1 | C_max is a bottleneck transportation problem
-- statement:
--   Consider $Q\mid res1{\cdot}1,\,p_j=1\mid C_{\max}$: $m$ uniform machines with speeds $q_i>0$, one resource of positive integer size $s_1$, $n$ unit-time jobs with requirements $r_{1j}\in\{0,1\}$, and no precedence constraints. Assume, as the paper does, that
--   $$q_h\ge q_i\qquad\text{for all } h=1,\dots,s_1 \text{ and all } i=s_1+1,\dots,m.$$
--   Then the minimum makespan equals the optimal value of the bottleneck transportation problem of the proof of Theorem 6, i.e. the minimum over slot assignments of $\max_{i,j,k} c_{ijk}x_{ijk}$:
--
--   1. for every feasible schedule $\sigma$ there is a slot assignment whose bottleneck value is at most $C_{\max}(\sigma)$;
--   2. for every slot assignment there is a feasible schedule whose $C_{\max}$ is at most its bottleneck value.
--
--   This is the content of the proof of Theorem 6: resource-requiring jobs may be restricted to the fastest $s_1$ machines, after which the scheduling problem is the bottleneck transportation problem, solvable in polynomial time.
--
--   **Formalization Note** Slot assignments are the 0–1 injective assignments of finite cost (see the slot-assignment definition). The two inclusions together say that both minima exist over the same values and coincide. For $s_1\ge m$ the speed hypothesis is vacuous and every machine may take resource jobs. The running time $O(n^3)$ is not formalized.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 17–18, proof of Theorem 6

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_SlotAssignment

namespace ResourceScheduling.Poly

/-- Proof of Theorem 6 (pp. 17–18): for `Q | res1·1, p_j = 1 | C_max` with the machines
`M_1, …, M_{s_1}` at least as fast as the others, the minimum `C_max` over feasible schedules
equals the optimal value of the bottleneck transportation problem: every feasible schedule is
matched by a slot assignment of bottleneck value at most its `C_max`, and every slot assignment
is realized by a feasible schedule of `C_max` at most its bottleneck value. -/
theorem q_res1dot1_bottleneck (I : Instance) (hl : I.l = 1) (hprec : I.NoPrecedence)
    (hr : ∀ j, I.r ⟨0, by omega⟩ j ≤ 1)
    (hfast : ∀ h i : Fin I.m, h.val < I.s ⟨0, by omega⟩ → I.s ⟨0, by omega⟩ ≤ i.val →
      I.q i ≤ I.q h) :
    (∀ σ : Schedule I, σ.Feasible →
        ∃ x, I.IsSlotAssignment hl x ∧ I.bottleneck x ≤ σ.makespan) ∧
      ∀ x, I.IsSlotAssignment hl x →
        ∃ σ : Schedule I, σ.Feasible ∧ σ.makespan ≤ I.bottleneck x := by sorry

end ResourceScheduling.Poly
