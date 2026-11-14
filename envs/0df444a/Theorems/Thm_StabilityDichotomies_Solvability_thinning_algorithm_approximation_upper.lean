-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinning_algorithm_approximation_upper
-- name    : StabilityDichotomies.Solvability.thinning_algorithm_approximation_upper
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:34:47.959539+00:00
-- url     : https://prove2.me/theorems/89a215f7-6f0f-477e-a710-d9e5ac178608
-- title:
--   Output-law formulation of the Horn and dual-Horn thinning upper bound
-- statement:
--   Let Γ be a finite Horn language, or a finite dual-Horn language, with b selecting the corresponding case. There is a constant C > 0 depending only on Γ and the case such that, for every 0 < ε ≤ 1, the solver given by the output law of Definition 4.2 satisfies at least a 1−ε fraction of constraints in expectation on every satisfiable input and has average sensitivity at most C/ε. In that output law, the retention probability is uniform on [1−ε,1], constraint occurrences are retained independently given that probability, and the output is respectively the least or greatest solution of the retained instance. This target formalizes the algorithm’s exact output distribution and guarantees, but does not formalize executable runtime; it is currently an open theorem.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.2 and Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinning_algorithm_approximation_upper (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, ThinningOutputLaw Γ b ε A ∧ Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  sorry
