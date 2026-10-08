-- Prove2me | Theorems.Thm_StochasticProg_LShaped_thm2_finite_convergence_v2
-- name    : StochasticProg.LShaped.thm2_finite_convergence_v2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:21:05.536477+00:00
-- url     : https://prove2.me/theorems/c6db00bb-3346-40df-9d15-a1d33cab5f65
-- title:
--   Chapter 5, Theorem 2 — finite convergence of the L-shaped algorithm (corrected)
-- statement:
--   Corrected version (v2) of Chapter 5, Theorem 2 (p. 198) of Birge & Louveaux, *Introduction to Stochastic Programming*: "When $\xi$ is a finite random variable, the L-shaped algorithm finitely converges to an optimal solution when it exists or proves the infeasibility of Problem (3.1.2)", $\min c^Tx+Q(x)$ s.t. $x\in K_1\cap K_2$.
--
--   Let $I$ be a two-stage recourse instance with $K$ finite scenarios such that
--   1. every realization has positive probability, $p_k>0$ (§5.1, p. 182: $k=1,\dots,K$ index the *possible* realizations);
--   2. the recourse matrix $W$ has full row rank $m_2$, so the bases of (1.5) and the simplex multipliers used in the proof (p. 197) exist;
--   3. the first-stage set $K_1$ is bounded — not stated in the book, but a sufficient condition for what Step 1 takes for granted ("let $(x^\nu,\theta^\nu)$ be an optimal solution", p. 183).
--
--   Then, starting from no cuts, **some** run of the algorithm's Step 1–2–3 transition (one taking optimal simplex bases, as the book's Steps 2–3 do) reaches, within at most as many steps as there are feasibility- and optimality-cut witnesses, a state where no further step applies, and there either the master problem is infeasible and $K_1\cap K_2=\varnothing$, or the master optimum $(x,\theta)$ has $x\in K_1\cap K_2$, passes every optimality test, and minimizes $c^Tx+Q(x)$ over $K_1\cap K_2$. ("Every run" would be false: the transition also admits bases that attain the value without being dual feasible.)
--
--   This replaces `StochasticProg.LShaped.thm2_finite_convergence`, which was disproved by an unbounded instance (neither an optimum nor infeasibility); the three hypotheses exclude that instance and the other counterexamples found when diagnosing it.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, Ch. 5 §5.1c Theorem 2, printed p. 198 (PDF p. 220); standing assumptions §5.1 pp. 182–184; proof pp. 196–198

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_StochasticProg_LShaped_Algorithm

namespace StochasticProg.LShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 5, Theorem 2 (p. 198): "When `ξ` is a finite random variable, the L-shaped
algorithm finitely converges to an optimal solution when it exists or proves the
infeasibility of Problem (3.1.2), namely, `min cᵀx + Q(x) s.t. x ∈ K1 ∩ K2`."

Formalized as: starting from no cuts at all, some run of the algorithm's Step-1-2-3
transition (`Step`) — one that takes optimal simplex bases, as the book's Steps 2–3 do — reaches, within a number of steps bounded by the finite total number of
feasibility- and optimality-cut witnesses available (`Fintype.card (Fin K × FeasBasis n2
m2) + Fintype.card (Fin K → Basis n2 m2)` — "there is only a finite number of different
combinations of the `K` multipliers ... because each corresponds to one of the finitely
many different bases", p. 220), a state from which no further `Step` cut can be added,
i.e. either the master problem has become infeasible (certifying `K1 ∩ K2 = ∅`) or its
optimum `x` is second-stage feasible, satisfies every fresh Step-3 termination test, and is
optimal for Problem (3.1.2).

v2 (2026-10-05): the published statement was disproved (an unbounded instance has neither an optimum nor infeasibility). This version adds three hypotheses. Every realization has positive probability (`hp_pos`): §5.1, p. 182, "k = 1, ..., K index its possible realizations". `W` has full row rank (`hW`), which the proof's "bases of (1.5)" and "simplex multipliers" (p. 197) presuppose. `K1` is bounded (`hK1`): not stated in the book, but a sufficient condition for what Step 1 takes for granted ("let (x^ν, θ^ν) be an optimal solution", p. 183); with it "an optimal solution when it exists" is automatic. The run is existential: the `Step` relation also admits bases that only attain the value without being dual feasible, so "every run" would be false. -/
theorem thm2_finite_convergence_v2 (inst : Instance n1 n2 m1 m2 K)
    (hp_pos : ∀ k, 0 < inst.p k)            -- §5.1: k indexes the possible realizations
    (hW : inst.W.rank = m2)                  -- (1.5) has bases / simplex multipliers
    (hK1 : Bornology.IsBounded (K1 inst)) :  -- Step 1's master LP has an optimal solution
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (Fin K × FeasBasis n2 m2) + Fintype.card (Fin K → Basis n2 m2) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsMasterInfeasible inst (path N).1 ∧ K1 inst ∩ K2 inst = ∅) ∨
        (∃ x θ, IsMasterOptimal inst (path N).1 (path N).2 x θ ∧
          x ∈ K1 inst ∩ K2 inst ∧
          (∀ β, IsOptimalAt inst x β →
            θ ≥ (optCutCoeffs inst β).2 - dotProduct (optCutCoeffs inst β).1 x) ∧
          ∀ x' ∈ K1 inst ∩ K2 inst, obj inst x ≤ obj inst x')) := by
  sorry

end StochasticProg.LShaped
