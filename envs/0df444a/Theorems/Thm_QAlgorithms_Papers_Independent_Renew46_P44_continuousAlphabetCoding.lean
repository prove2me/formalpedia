-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_continuousAlphabetCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.continuousAlphabetCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:35:18.060109+00:00
-- url     : https://prove2.me/theorems/f3966982-f4f5-43f6-8ecc-7ae221107b57
-- title:
--   Proposition 2 with (63): continuous-alphabet constrained capacity
-- statement:
--   Let $A$ be any Borel subset of a finite-dimensional Euclidean space, and let $x\mapsto S_x$ be weak-operator continuous normalized trace-class states on a nonzero complex Hilbert space. Assume uniformly bounded individual entropies, a nonnegative lower-semicontinuous cost $f$, a finite budget $E$, and a nonempty admissible discrete-law class. Under the per-word constraint $\sum_k f(x_k)\le nE$,
--
--   $$C=\bar C=\sup_{\pi:\,\int_A f\,d\pi\le E}\int_A D(S_x\Vert\bar S_\pi)\,\pi(dx),\qquad
--   \bar S_\pi=\int_A S_x\,\pi(dx).$$
--
--   The last supremum ranges over Borel probability measures and equals the supremum over countably supported laws. No closedness of $A$, finite capacity, or bounded mixture entropy is assumed. The factor $n$ corrects the omission in printed (61).
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 21, Proposition 2 with (63): continuous-alphabet constrained capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2 together with (63), PDF pp.20-22. A is any Borel subset,
not assumed closed or compact. On uniformly bounded positive density families,
continuity of all basis coefficients is equivalent to weak-operator continuity.
Printed (61) has E; changed to nE in cqError, as required by (54),(60),
the explicit application of Theorem 4, and the later power constraint (123). -/
theorem continuousAlphabetCoding (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : MeasurableSet A) {I : Type} [Nonempty I]
    (S : A → Matrix I I ℂ) (hS : ∀ a, TC.IsDensity (S a))
    (hcontinuous : ∀ i j, Continuous (fun a => S a i j))
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hlsc : LowerSemicontinuous f)
    (E : ℝ) (hfeasible : ∃ pi : DiscreteInputLaw A, HasMeanCostBound f E pi)
    (hentropy : BoundedLetterEntropy S) :
    averageErrorCqCapacity S f E = cqHolevoSingle S f E ∧
    cqHolevoSingle S f E =
      ⨆ pi : {pi : Measure A // AdmissibleMeasure f E pi}, integralChi S pi.val := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
