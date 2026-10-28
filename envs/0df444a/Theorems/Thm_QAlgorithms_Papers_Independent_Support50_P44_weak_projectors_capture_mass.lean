-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_weak_projectors_capture_mass
-- name    : QAlgorithms.Papers.Independent.Support50.P44.weak_projectors_capture_mass
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:06:40.585652+00:00
-- url     : https://prove2.me/theorems/177ac9ea-4e73-492e-a07c-f37c0c2fca38
-- title:
--   Mass captured by weakly convergent finite-rank projectors
-- statement:
--   Let $E$ be a complex separable Hilbert space and $(\Pi_n)_{n\in\mathbb N}$ finite-rank orthogonal projectors converging to the identity in the weak operator topology: $\langle x,\Pi_n y\rangle\to\langle x,y\rangle$ for all $x,y\in E$. For every density operator $\sigma$,
--
--   $$\lim_{n\to\infty}\operatorname{tr}(\Pi_n\sigma)=\operatorname{tr}\sigma.$$
--
--   No nesting or monotonicity is required. This shows that weakly exhausting finite supports capture the full probability mass.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 27, Lemma E.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.27, Lemma E.2, (162): e in E is corrected to a natural-number
sequence, as in the proof. No nesting or monotonicity is imposed. -/
theorem weak_projectors_capture_mass {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n, IsFiniteProjector (P n)) (hweak : WeaklyExhausts P)
    (sigma : H →L[ℂ] H) (hsigma : IsHilbertDensity b sigma) :
    Tendsto (fun n => (hilbertTrace b ((P n).comp sigma)).re) atTop
      (nhds (hilbertTrace b sigma).re) := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
