-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_C_2
-- name    : SubquadCutReach.Faster.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:45.72897+00:00
-- url     : https://prove2.me/theorems/d5c113c0-c385-4c37-810f-3c1c9d9ae83e
-- title:
--   Lemma C.2 — Explicit integral maximum flow
-- statement:
--   Let $D$ be a known rule, $b^*$ a feasible target on $H$, and $\Delta=\|b_D-b^*\|_1$. In the constructed repair network $N$, with fresh source and sink and unit internal capacities,
--
--   $$\max\operatorname{val}(f)=\Delta/4.$$
--
--   A uniform deterministic program returns an explicit integral maximum-flow matrix using at most $C(n^{5/3}+n\sqrt\Delta)L(n)^p$ cut queries to $H$, for absolute $C>0$ and fixed $p$. Terminal capacities are allowed to exceed one. The maximization compares against all real feasible flows. Both the value identity and explicit recovery are included; no adjacency oracle or realizing orientation is supplied.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 27, Lemma C.2 (PDF p. 29)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_C_2 :
    (∀ i : RepairCase, ∃ f : Node i.n → Node i.n → ℝ,
      MaximumFlow (capacity i.H i.D i.b) f ∧ flowValue f = error i.H i.D i.b/4) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ P : Program, Admissible P ∧ Deterministic P ∧
      ∀ i : RepairCase, RunsWithin P (cut i.H) (repairInput i.b i.D)
        (fun m => MaximumFlow (capacity i.H i.D i.b) (outputFlow i.n m) ∧
          IntegralFlow (outputFlow i.n m))
        (C*(scale i.n+i.n*Real.sqrt (error i.H i.D i.b))*L i.n^p) := by sorry

end SubquadCutReach.Faster
