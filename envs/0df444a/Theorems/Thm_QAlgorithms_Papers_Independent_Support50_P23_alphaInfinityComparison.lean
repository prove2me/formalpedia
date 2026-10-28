-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaInfinityComparison
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaInfinityComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:08:14.80837+00:00
-- url     : https://prove2.me/theorems/7c999a9d-13d9-46eb-a0f5-b9df5271a55c
-- title:
--   Regularized spectral formula and min-entropy comparison
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states and write $\rho_{AB}=\sum_i\nu_i|i\rangle\langle i|$ and $I_A\otimes\sigma_B=\sum_j\mu_j|\bar j\rangle\langle\bar j|$ in orthonormal eigenbases. Then
--   $$
--   \lim_{\xi\downarrow0}-\log_2\max_{i,j:\langle i|\bar j\rangle\ne0}
--   \frac{\nu_i}{\mu_j+\xi}
--   =H_\infty(A|B)_{\rho|\sigma}\le H_{\min}(A|B)_{\rho|\sigma}.
--   $$
--   The limit is extended-real convergence and the maximum retains its overlap restriction. This compares the limiting Petz entropy with fixed-reference min entropy.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Section II, unnumbered: order-infinity spectral comparison

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

/-- Section II, PDF p.4: overlap-restricted regularized spectral maximum and its
comparison with fixed-reference min entropy, including singular sigma. -/
theorem alphaInfinityComparison [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (s t : NonnegativeSpectralDecomposition (A × B)) (hs : s.operator = rho)
    (ht : t.operator = identityTensorReference (A := A) sigma) :
    Tendsto (spectralLog s t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (alphaEntropy rho sigma ⊤)) ∧
      alphaEntropy rho sigma ⊤ ≤ fixedMin rho sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
