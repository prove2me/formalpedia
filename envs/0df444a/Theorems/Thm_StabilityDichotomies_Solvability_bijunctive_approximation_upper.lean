-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_bijunctive_approximation_upper
-- name    : StabilityDichotomies.Solvability.bijunctive_approximation_upper
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:25:08.998524+00:00
-- url     : https://prove2.me/theorems/75859cbe-074d-47ee-a3d5-6f41a3aa0244
-- title:
--   Semantic existential consequence of the bijunctive upper bound
-- statement:
--   For every finite bijunctive Boolean language $\Gamma$, there is a constant $C_\Gamma>0$ such that, for each $0<\varepsilon\le1$, some solver $(1-\varepsilon)$-approximates all satisfiable instances and has average sensitivity at most $C_\Gamma\varepsilon^{-1}\log n$ on satisfiable instances with $n\ge2$ variables. Bijunctivity is expressed by coordinatewise-majority closure. **Scope:** this is a semantic existential consequence of Theorem 4.9; the `Solver` type does not encode the particular algorithm of Definition 4.8 or a runtime guarantee.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Theorem 4.9, p.19; semantic existential consequence only.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem bijunctive_approximation_upper (Γ : Language)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  sorry

end StabilityDichotomies.Solvability
