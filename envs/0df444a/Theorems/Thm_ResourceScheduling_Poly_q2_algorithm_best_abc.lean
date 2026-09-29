-- Prove2me | Theorems.Thm_ResourceScheduling_Poly_q2_algorithm_best_abc
-- name    : ResourceScheduling.Poly.q2_algorithm_best_abc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:32:05.695161+00:00
-- url     : https://prove2.me/theorems/db6f0b29-ee41-47a0-b36f-22913c0a35e0
-- title:
--   Proof of Theorem 5 — the algorithm is best among schedules with properties (a), (b), (c)
-- statement:
--   Consider $Q2\mid res1{\cdot}{\cdot},\,p_j=1\mid C_{\max}$: two uniform machines $M_1,M_2$ with speeds $q_1\ge q_2>0$, one resource of positive integer size $s_1$, $n$ unit-time jobs with nonnegative integer requirements $r_{1j}\le s_1$, and no precedence constraints. Let $\pi$ be any order of the jobs with nonincreasing requirements, and let $A$ be the schedule produced by the algorithm of Theorem 5 from $\pi$.
--
--   Then $A$ is feasible, satisfies properties (a), (b) and (c), and
--   $$C_{\max}(A)\le C_{\max}(\sigma)$$
--   for every feasible schedule $\sigma$ satisfying (a), (b) and (c).
--
--   This is the first half of the paper's proof of Theorem 5: "This O(n log n) algorithm clearly generates the best schedule among those satisfying the following properties". Combined with the exchange argument (every feasible schedule can be turned into an (a)–(c) schedule that is at least as good), it gives the optimality of the algorithm.
--
--   **Formalization Note** The hypothesis $r_{1j}\le s_1$ (every job fits alone) is implicit in the paper; without it no feasible schedule exists. The running time is not formalized.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 5 ("This O(n log n) algorithm clearly generates the best schedule among those satisfying the following properties")

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties
import Definitions.Def_ResourceScheduling_Poly_Q2Algorithm

namespace ResourceScheduling.Poly

/-- Proof of Theorem 5 (p. 16): the algorithm generates the best schedule among those satisfying
properties (a), (b) and (c). -/
theorem q2_algorithm_best_abc (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (hprec : I.NoPrecedence) (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (hfit : I.EveryJobFits)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) :
    (q2Algorithm I hm hl ord).Feasible ∧ (q2Algorithm I hm hl ord).SatisfiesABC hm hl ∧
      ∀ σ : Schedule I, σ.Feasible → σ.SatisfiesABC hm hl →
        (q2Algorithm I hm hl ord).makespan ≤ σ.makespan := by sorry

end ResourceScheduling.Poly
