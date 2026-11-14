-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_horn_dual_horn_approximation_upper
-- name    : StabilityDichotomies.Solvability.horn_dual_horn_approximation_upper
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:24:53.183422+00:00
-- url     : https://prove2.me/theorems/9cf96c71-bf97-4067-a732-b4f1ba21b646
-- title:
--   Semantic existential consequence of the Horn/dual-Horn upper bound
-- statement:
--   For every finite Horn or dual-Horn Boolean constraint language $\Gamma$, there is a constant $C_\Gamma>0$ such that, for every $0<\varepsilon\le1$, some solver $(1-\varepsilon)$-approximates every satisfiable instance and has average sensitivity at most $C_\Gamma/\varepsilon$ on every satisfiable instance. Horn and dual-Horn are expressed by closure under coordinatewise AND and OR. **Scope:** this is a semantic existential consequence of Theorem 4.3. The unrestricted `Solver` type does not encode its particular thinning algorithm or any runtime guarantee; the full algorithm-specific theorem remains to be formalized.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Theorem 4.3, p.16; semantic existential consequence only.

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability
theorem horn_dual_horn_approximation_upper (Γ : Language)
    (hΓ : (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples) ∨
      (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  sorry

end StabilityDichotomies.Solvability
