-- Prove2me | Theorems.Thm_SkutellaCQP_MaxSNP_l_reduction
-- name    : SkutellaCQP.MaxSNP.l_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:02.556023+00:00
-- url     : https://prove2.me/theorems/681d5c94-bd1a-46b7-a224-b1a226966056
-- title:
--   Lemma 7.1 b) and proof of Theorem 7.2, p. 33 — 3-Occurrence Max3Sat L-reduces to R | rⱼ | Σ Cⱼ with α = 32, β = 1
-- statement:
--   Let $I$ be an instance of 3-OCCURRENCE MAX3SAT with $n$ variables and $m$ clauses, and let $R(I)$ be the instance of $R\,|\,r_j\,|\sum C_j$ constructed from it: for each variable a v-job of length $4$, released at $0$, that may run only on the variable's true or false machine; for each clause a c-job of length $0$, released at $3$, that may run on the false machine of each variable occurring nonnegated in the clause and on the true machine of each variable occurring negated. Then $R(I)$ has an optimal schedule $S_0$, and
--
--   1. $\mathrm{OPT}_{\mathrm{SCH}}(R(I))=\mathrm{VAL}(S_0)=4n+4m-\mathrm{OPT}_{\mathrm{SAT}}(I)$ (Lemma 7.1 b));
--   2. $\mathrm{OPT}_{\mathrm{SCH}}(R(I))\le 32\,\mathrm{OPT}_{\mathrm{SAT}}(I)$;
--   3. for every feasible schedule $S$ of $R(I)$,
--   $$
--   \mathrm{OPT}_{\mathrm{SAT}}(I)-\#(\mathrm{SAT}(S))\ \le\ \mathrm{VAL}(S)-\mathrm{OPT}_{\mathrm{SCH}}(R(I)).
--   $$
--
--   Items 2 and 3 are the two conditions of an L-reduction with constants $\alpha=32$ and $\beta=1$. With the MaxSNP-hardness of 3-OCCURRENCE MAX3SAT they give the MaxSNP-hardness of $R\,|\,r_j\,|\sum C_j$ (Theorem 7.2, due to Hoogeveen, Schuurman and Woeginger 1998).
--
--   **Formalization Note** MaxSNP-hardness, polynomial-time computability of $R$ and of $\mathrm{SAT}$, and the definition of an L-reduction are not formalized; the statement is the mathematical content of the two L-reduction conditions for this particular reduction. $\mathrm{OPT}_{\mathrm{SCH}}$ is not a primitive: the theorem asserts a feasible schedule $S_0$ that is no worse than every feasible schedule. The validity hypothesis on $I$ includes two conventions not written on the page (clauses have one to three literals; every variable occurs); without the second, the constant $32$ fails, since a variable that occurs nowhere adds $4$ to $\mathrm{OPT}_{\mathrm{SCH}}$ and nothing to $\mathrm{OPT}_{\mathrm{SAT}}$.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 33, Lemma 7.1 b) and proof of Theorem 7.2

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

namespace SkutellaCQP.MaxSNP

/-- Lemma 7.1 b) and the two L-reduction conditions of the proof of Theorem 7.2 (p. 33), with
`α = 32` and `β = 1`: `R(I)` has an optimal schedule `S₀` with
`VAL(S₀) = 4n + 4m − OPT_SAT(I) ≤ 32 · OPT_SAT(I)`, and every feasible schedule `S` satisfies
`OPT_SAT(I) − #(SAT(S)) ≤ VAL(S) − VAL(S₀)`. -/
theorem l_reduction {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid) :
    ∃ S₀ : Sched n m, Feasible I S₀ ∧ VAL S₀ = (4 * n + 4 * m : ℝ) - optSat I ∧
      (∀ S, Feasible I S → VAL S₀ ≤ VAL S) ∧ VAL S₀ ≤ 32 * optSat I ∧
      ∀ S, Feasible I S → (optSat I : ℝ) - satCount I (SAT S) ≤ VAL S - VAL S₀ := by sorry

end SkutellaCQP.MaxSNP
