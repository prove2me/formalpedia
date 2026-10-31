-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_compatibility_implies_positive_difference
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.compatibility_implies_positive_difference
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:16:41.732729+00:00
-- url     : https://prove2.me/theorems/9f516449-c38d-4167-b44d-8276d072a4ae
-- title:
--   Compatibility implies a positive difference map
-- statement:
--   Let $\Phi$ be a complex-linear completely positive map on $2\times2$ complex matrices satisfying $\Phi(I)\le I$ and $\Phi^*(I)\le I$, and let $V$ satisfy $VV^\dagger\le I$. Suppose every positive semidefinite matrix $S$ and every Jones vector $\alpha$ satisfy
--
--   $$S\ge\alpha\alpha^\dagger\quad\Longrightarrow\quad\Phi(S)\ge V\alpha\alpha^\dagger V^\dagger.$$
--
--   Then $\Phi-(X\mapsto VXV^\dagger)$ is positive: it maps every positive semidefinite matrix to a positive semidefinite matrix. This is the forward implication after (54) for abstract admissible pairs.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 9, §VI.B, after (54): positivity of the difference map

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF p.9, immediately after (54): compatibility
on every admissible, unnormalized Stokes–Jones pair implies positivity of the
difference map. This is the stated forward implication, without a converse. -/
theorem compatibility_implies_positive_difference
    (Phi : PolarizationMatrix →ₗ[ℂ] PolarizationMatrix) (V : PolarizationMatrix)
    (hPhi : IsDoublyContracting Phi) (hV : (1 - V * Vᴴ).PosSemidef)
    (hcompatible : ∀ (S : PolarizationMatrix) (alpha : JonesVector),
      S.PosSemidef → (S - jonesOuter alpha).PosSemidef →
        (Phi S - V * jonesOuter alpha * Vᴴ).PosSemidef) :
    IsPositiveMap (Phi - jonesConjugation V) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
