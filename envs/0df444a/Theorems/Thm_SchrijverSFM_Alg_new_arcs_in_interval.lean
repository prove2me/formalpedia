-- Prove2me | Theorems.Thm_SchrijverSFM_Alg_new_arcs_in_interval
-- name    : SchrijverSFM.Alg.new_arcs_in_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:42.010801+00:00
-- url     : https://prove2.me/theorems/9000199a-6ee8-4e16-bb01-a9092b416b65
-- title:
--   Display (22), §5, p. 352 — every new arc (v, w) ∈ A′ \ A satisfies s ≼₁ w ≺₁ v ≼₁ t
-- statement:
--   Let $S \to S'$ be one iteration of the algorithm with chosen elements $t, s$ and chosen order $\prec_1$ (the $i$-th order of $S$, with weight $\lambda_1$). Let $A$ and $A'$ be the arc sets of the digraphs of $S$ and $S'$. Then for each arc $(v, w) \in A' \setminus A$,
--   $$s \preceq_1 w \prec_1 v \preceq_1 t.$$
--
--   New arcs arise only from the moved orders $\prec_1^{s,u}$ and lie inside the interval $[s, t]$ of $\prec_1$. This is the key structural fact of the running-time analysis: it shows that distances never decrease (20) and that no new arc enters $t$.
--
--   **Formalization Note** The order $\prec_1$ and its weight are named through the hypothesis that the $i$-th entry of $S$ is $(\prec_1, \lambda_1)$. No submodularity is needed.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 352, display (22)

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem new_arcs_in_interval {n : ℕ} (f : Finset (Fin n) → ℝ)
    (S S' : State n) (t s : Fin n) (i : ℕ) (hstep : StepVia f S S' t s i)
    (σ₁ : Equiv.Perm (Fin n)) (lam₁ : ℝ) (hi : S[i]? = some (σ₁, lam₁)) :
    ∀ v w : Fin n, arc S' v w → ¬ arc S v w →
      σ₁ s ≤ σ₁ w ∧ σ₁ w < σ₁ v ∧ σ₁ v ≤ σ₁ t := by sorry
end SchrijverSFM.Alg
