-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_regularisedMaximum
-- name    : QAlgorithms.Papers.Independent.Support50.P17.regularisedMaximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:58:38.478922+00:00
-- url     : https://prove2.me/theorems/ddfbfff5-c299-47c8-9071-b62c764a4e07
-- title:
--   Maximum of the shifted relative entropy
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on the same nonzero finite-dimensional complex Hilbert space. Write $I$ for the identity and $S(A\|B)=\operatorname{Tr}A(\log A-\log B)$ for the unnormalised Umegaki relative entropy, with natural logarithms, zero spectral weights contributing zero, and value $+\infty$ on failure of support containment. Then
--
--   $$
--   S(\rho+I\|\sigma+I)\le\log 2.
--   $$
--
--   Equality holds whenever both densities have rank one and $\rho\sigma=0$. Such orthogonal pure densities attaining equality exist in every dimension $d\ge2$. The inequality also holds in dimension one.
--
--   This identifies the global maximum before any normalization constant is applied; the shifted matrices are not divided by their trace.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 2, §I, unnumbered: maximum of the shifted relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.2, Section I: the global log 2 maximum and equality for orthogonal pure
states. Such witnesses exist in every dimension d≥2; dimension one retains the bound. -/
theorem regularisedMaximum :
    (∀ {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
      (rho sigma : Matrix I I ℂ), IsDensityMatrix rho → IsDensityMatrix sigma →
      relativeEntropy (rho + 1) (sigma + 1) ≤ (Real.log 2 : EReal) ∧
        (rho.rank = 1 → sigma.rank = 1 → rho * sigma = 0 →
          relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal))) ∧
    (∀ d : ℕ, 2 ≤ d → ∃ rho sigma : Matrix (Fin d) (Fin d) ℂ,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      rho.rank = 1 ∧ sigma.rank = 1 ∧ rho * sigma = 0 ∧
      relativeEntropy (rho + 1) (sigma + 1) = (Real.log 2 : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
