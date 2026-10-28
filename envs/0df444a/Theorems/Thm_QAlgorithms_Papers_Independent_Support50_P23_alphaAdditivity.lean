-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaAdditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:07:24.414274+00:00
-- url     : https://prove2.me/theorems/e1c81ca5-fa15-443d-a8d0-097df2df8728
-- title:
--   Binary and i.i.d. tensor additivity
-- statement:
--   Let $\rho_{AB},\tau_{CD}$ and reference states $\sigma_B,\omega_D$ be normalized on arbitrary finite-dimensional nonzero complex systems. For every $\alpha\in[0,\infty]$, with factors regrouped as $AC,BD$,
--   $$
--   H_\alpha(AC|BD)_{\rho\otimes\tau|\sigma\otimes\omega}
--   =H_\alpha(A|B)_{\rho|\sigma}+H_\alpha(C|D)_{\tau|\omega}.
--   $$
--   In particular, for every integer $n\ge1$,
--   $$
--   H_\alpha(A^n|B^n)_{\rho^{\otimes n}|\sigma^{\otimes n}}
--   =nH_\alpha(A|B)_{\rho|\sigma}.
--   $$
--   The two factors can have different dimensions. These identities are the product scaling used in the finite-block bound.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Section II, unnumbered: tensor additivity, (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Section II, PDF p.4, (18): arbitrary binary tensor additivity and its displayed
i.i.d. specialization for positive n, including all endpoint orders. -/
theorem alphaAdditivity [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (alpha : ℝ≥0∞) :
    (∀ {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
      [Nonempty C] [Nonempty D]
      (tau : Matrix (C × D) (C × D) ℂ) (omega : Matrix D D ℂ),
      IsDensityMatrix tau → IsDensityMatrix omega →
        alphaEntropy (independentProduct rho tau) (Matrix.kronecker sigma omega) alpha =
          alphaEntropy rho sigma alpha + alphaEntropy tau omega alpha) ∧
    (∀ n : ℕ, 0 < n →
      alphaEntropy (jointPower rho n) (matrixPower sigma n) alpha =
        n • alphaEntropy rho sigma alpha) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
