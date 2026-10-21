-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundSquashedFaithfulness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundSquashedFaithfulness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:39:34.011403+00:00
-- url     : https://prove2.me/theorems/f838f14e-ba48-40a1-9792-f4cd19ca835a
-- title:
--   Squashed entanglement vanishes exactly on separable states
-- statement:
--   For every density operator $\rho_{AC}$ on nonzero finite-dimensional systems, with the infimum defining squashed entanglement taken over extensions in all finite ancillary dimensions,
--
--   $$E_{\rm sq}(\rho_{AC})=0\quad\Longleftrightarrow\quad\rho_{AC}\in\mathcal S_{A:C}.$$
--
--   Here $\mathcal S_{A:C}$ is the set of finite convex mixtures of product density operators, the finite-dimensional separable states. This is the background faithfulness claim explicitly stated before Appendix D's quantitative bounds.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 26, BackgroundSquashedFaithfulness

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Squashed entanglement is faithful (PDF p.26), finite-system background claim. -/
theorem backgroundSquashedFaithfulness {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (rho : Op (A × C)) (hrho : IsDensityMatrix rho) :
    squashedEntanglement rho = 0 ↔ QAlgorithms.Entanglement.IsSeparableDensity rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
