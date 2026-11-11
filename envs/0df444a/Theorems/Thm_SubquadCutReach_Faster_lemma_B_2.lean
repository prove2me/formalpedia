-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_B_2
-- name    : SubquadCutReach.Faster.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:45.109875+00:00
-- url     : https://prove2.me/theorems/21234b18-de0f-44af-aedf-e86bfe323765
-- title:
--   Lemma B.2 — Completing a partial orientation
-- statement:
--   Let $R\subseteq E(J)$ be explicit reserved edges, and let $D_0$ orient every unreserved edge. Suppose
--
--   $$\left|\sum_{v\in S}b_{D_0}(v)\right|\le C_R(S)\qquad\text{for every }S\subseteq V.$$
--
--   A uniform deterministic finite program, supplied only with $R$ and $b_{D_0}$, computes directions for reserved edges so that the extension $D$ obeys $|b_D(v)|\le1$ at every vertex. Unreserved directions are retained. The program has no access to the unknown graph; a constant zero oracle is provided. This separates explicit completion from learning the reserve.
--
--   Differences from the source:
--   - encoding: labelled graphs and orientation rules → Fin n, Mathlib simple graphs and increasing-pair Boolean tables; reason: all finite labelled source graphs and all directions are represented; unused table cells carry no mathematical information
--   - encoding: completion uses only explicit R and the vector b_D0 → a uniform deterministic program with precisely that input and a constant-zero oracle returns the reserved-edge directions; reason: the hidden unreserved graph and its directions are not algorithm inputs; the mathematical extension retains those directions
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 25, Lemma B.2 (PDF p. 27)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false
open scoped BigOperators

namespace SubquadCutReach.Faster

/-- The completion program receives R and b_D0 only. It gets no hidden-graph oracle. -/
theorem lemma_B_2 :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧
      ∀ (n : ℕ) (J : SimpleGraph (Fin n)) (R : Finset (Fin n × Fin n)) (D₀ : Rule n),
        R ⊆ pairs J → CompletionCondition J R D₀ →
        ∀ ω : ℕ → Bool, ∃ t : ℕ,
          (run P (fun _ : Finset (Fin n) => 0)
            (completionInput R (imbalance (induced (remove J R) D₀))) ω t).halted = true ∧
          let m := (run P (fun _ : Finset (Fin n) => 0)
            (completionInput R (imbalance (induced (remove J R) D₀))) ω t).core.mem
          let D : Rule n := fun u v => if (u,v) ∈ R then outputRule n m u v else D₀ u v
          (∀ v, |imbalance (induced J D) v| ≤ 1) := by sorry

end SubquadCutReach.Faster
