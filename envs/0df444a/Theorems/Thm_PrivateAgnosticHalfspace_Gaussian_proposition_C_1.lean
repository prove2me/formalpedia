-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_proposition_C_1
-- name    : PrivateAgnosticHalfspace.Gaussian.proposition_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:30.962375+00:00
-- url     : https://prove2.me/theorems/710d6e59-0655-4e3d-ac32-bdb292f09181
-- title:
--   Proposition C.1 — privacy of Algorithm 1
-- statement:
--   Let Algorithm 1 use positive public numbers of training blocks, thresholds and validation examples, with training-block size at least two. Use a measurable $(\varepsilon,\delta)$-DP regression routine with unit-ball outputs, where $\varepsilon,\delta\in(0,1/2]$. Its independent training runs and exponential validation produce a probability mechanism $A$ satisfying, for every deterministic neighboring pair $S,S'$ and every measurable output event $E$,
--   $$
--   \Pr[A(S)\in E]\le e^{\varepsilon}\Pr[A(S')\in E]+\delta.
--   $$
--   The output law is exactly the defined composition of disjoint ordered blocks, independent optimizer laws and validation weights. There is no assumption on a population distribution or on the values of the dataset.
--
--   This is the dataset-level privacy assertion needed by the headline theorem. The regression routine's privacy is the interface supplied by Lemma B.4; the headline theorem establishes its existence and its guarantees as conclusions.
--
--   Differences from the source:
--   - generalization: Algorithm 1 with its prescribed public degree and block schedule and the private optimizer of B.4 → any natural dimension and degree, positive public block/grid/validation sizes, training-block size at least two, and any measurable private unit-ball optimizer; reason: privacy uses only disjoint public blocks and the stated optimizer interface; the headline schedule and its existential optimizer specialize this assertion
--   - encoding: the optimizer used in Algorithm 1 is the private routine from B.4 → explicit measurability and DP binders for that subroutine; reason: these describe the called routine, rather than adding a population assumption; no optimizer premise appears in the headline theorem
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 24, Proposition C.1; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

/-- Algorithm 1 privacy on every deterministic input. The interface assumption is exactly
that its called regression routine is private; no population law is an input. -/
theorem proposition_C_1 (O : Optimizer) (d p k M n₀ m : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hn : 2 ≤ n₀) (hm : 0 < m)
    (ε δ : ℝ) (hε : 0 < ε ∧ ε ≤ 1 / 2) (hδ : 0 < δ ∧ δ ≤ 1 / 2)
    (hOmeas : Measurable (fun S => (O d p n₀ ε δ S : Measure (UnitBall d p))))
    (hOprivate : PrivateUniformGen.Characterization.IsDP (O d p n₀ ε δ) ε δ) :
    ∃ A : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) (k * n₀ + m),
      (∀ S, (A S : Measure (Output d p M)) = algorithmLaw O d p k M n₀ m ε δ S) ∧
      Measurable (fun S => (A S : Measure (Output d p M))) ∧
      PrivateUniformGen.Characterization.IsDP A ε δ := by sorry

end PrivateAgnosticHalfspace.Gaussian
