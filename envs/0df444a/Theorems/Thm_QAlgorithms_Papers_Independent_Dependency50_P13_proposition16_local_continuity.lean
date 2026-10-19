-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_proposition16_local_continuity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.proposition16_local_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:13:18.485752+00:00
-- url     : https://prove2.me/theorems/81a1a20c-18af-4e2b-8f41-76c84f319ba1
-- title:
--   Proposition 16: two sufficient conditions for local continuity
-- statement:
--   Let H be a nonzero separable complex Hilbert space, and let F be a nonempty state set with compact-test weak* closed cone. Suppose rho_n tends to rho in trace norm. Then
--
--   $$ D_F(\rho_n)\longrightarrow D_F(\rho)\in[0,+\infty] $$
--
--   provided either of the following holds. First, rho_n=Phi_n(rho)/Tr Phi_n(rho), where every Phi_n is a positive trace-nonincreasing complex-linear map on trace-class operators, maps F into cone(F) intersected with the trace unit ball, has positive success trace on rho, and these traces tend to one. Alternatively, there are real c_n tending to one and states sigma_n such that c_n rho_n<=sigma_n for every n and D_F(sigma_n) tends to D_F(rho).
--
--   No all-index positivity condition is imposed on c_n in the second alternative. The result gives two sufficient conditions for local continuity of the extended distance.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 16, Proposition 16: two sufficient conditions for local continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Proposition 16, arXiv:2105.08091v3, PDF pp.16–17, (61)–(63).
Section III C supplies lower semicontinuity via the weak-star closed cone. In (a) the success
traces are positive, enforcing normalization's domain. In (b), c_n are arbitrary real numbers. -/
theorem proposition16_local_continuity [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (F : Set (State b)) (hF : F.Nonempty)
    (hcone : WeakStarClosedCone F) (rhoSeq : ℕ → State b) (rho : State b)
    (hrho : TraceTendsto rhoSeq rho)
    (hcondition :
      (∃ Phi : ℕ → (H →L[ℂ] H) → (H →L[ℂ] H),
        (∀ n, PositiveTraceNonIncreasing b (Phi n) ∧ FreeSubnormalisedOutputs F (Phi n)) ∧
        (∀ n, 0 < (operatorTrace b (Phi n rho.val.val)).re ∧
          Phi n rho.val.val = ((operatorTrace b (Phi n rho.val.val)).re : ℂ) •
            (rhoSeq n).val.val) ∧
        Tendsto (fun n => (operatorTrace b (Phi n rho.val.val)).re) atTop (nhds 1)) ∨
      (∃ c : ℕ → ℝ, ∃ sigma : ℕ → State b,
        Tendsto c atTop (nhds 1) ∧
        (∀ n, IsPositive ((sigma n).val.val - (c n : ℂ) • (rhoSeq n).val.val)) ∧
        Tendsto (fun n => resourceDistance F (sigma n)) atTop (nhds (resourceDistance F rho)))) :
    Tendsto (fun n => resourceDistance F (rhoSeq n)) atTop (nhds (resourceDistance F rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
