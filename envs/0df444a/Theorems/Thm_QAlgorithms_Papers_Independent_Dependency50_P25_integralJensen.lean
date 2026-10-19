-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P25_integralJensen
-- name    : QAlgorithms.Papers.Independent.Dependency50.P25.integralJensen
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:17:19.539982+00:00
-- url     : https://prove2.me/theorems/7a1c94d3-d3bc-44ea-b8e7-9952c9ea046a
-- title:
--   Integral Jensen inequality for extended costs
-- statement:
--   Let $A$ be a closed, bounded, convex subset of a separable real Banach space $E$, and let $f:A\to[-\infty,+\infty]$ be convex. Suppose either that $f$ is lower semicontinuous, or that $f$ is upper semicontinuous and bounded above by a finite real constant. For every Borel probability measure $\mu$ on $A$,
--
--   $$
--   f\!\left(\int_A x\,\mu(dx)\right)\le\int_A f(x)\,\mu(dx).
--   $$
--
--   The vector integral is the Bochner barycenter; the cost integral is an extended Lebesgue expectation. No finite expectation or global continuity is assumed. This is the continuous-ensemble Jensen inequality used in the convex-roof construction.
-- source:
--   On properties of the space of quantum states and their application to construction of entanglement monotones, arXiv:0804.1515v4, PDF p. 31, Proposition A-2: integral Jensen inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P25

/-- Proposition A-2 (integral Jensen inequality), arXiv:0804.1515v4,
PDF p.31, Eq.(27). Both alternatives are retained: lower semicontinuity,
or upper boundedness together with upper semicontinuity. The probability
is on the Borel subspace of the closed bounded convex Banach domain.
No finite-valuedness, continuity or integrability of the cost is assumed. -/
theorem integralJensen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (A : Set E) (hclosed : IsClosed A) (hbounded : Bornology.IsBounded A)
    (f : E → EReal) (hconvex : extendedConvexOn A f)
    (hregular : LowerSemicontinuous (fun x : A => f x) ∨
      ((∃ M : ℝ, ∀ x ∈ A, f x ≤ (M : EReal)) ∧
        UpperSemicontinuous (fun x : A => f x)))
    (mu : Measure A) [IsProbabilityMeasure mu] :
    f (banachBarycenter mu) ≤ extendedIntegral mu (fun x : A => f x) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P25

end
