-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P12_independent_additivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P12.independent_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:20:57.877374+00:00
-- url     : https://prove2.me/theorems/b8088192-fd56-4ceb-a60d-084f34d86e0e
-- title:
--   §I C, implications: additivity for independent systems
-- statement:
--   All registers are finite-dimensional complex Hilbert spaces of positive dimension, represented in arbitrary orthonormal bases. States are positive semidefinite operators of trace one. All logarithms are binary, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Conditional min-entropy optimizes the operator-order definition over every normalized reference state; conditional max-entropy is defined by purification duality.
--
--   Let $\rho_{AB}$ and $\omega_{CD}$ be arbitrary states of two independent systems. Construct their product and regroup its registers as $AC$ and $BD$. Then
--   $$H_{\min}(AC|BD)_{\rho\otimes\omega}=H_{\min}(A|B)_\rho+H_{\min}(C|D)_\omega,$$
--   $$H_{\max}(AC|BD)_{\rho\otimes\omega}=H_{\max}(A|B)_\rho+H_{\max}(C|D)_\omega.$$
--   These are both equalities for the constructed product state. They express additivity for independent systems.
-- source:
--   The operational meaning of min- and max-entropy, arXiv:0807.1338v2, PDF p. 6, Section I C, implications

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.6, implications: both entropy equalities for the actual independent
product regrouped as AC given BD. -/
theorem independent_additivity [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (omega : Matrix (C × D) (C × D) ℂ) (homega : IsDensityMatrix omega) :
    conditionalMinEntropy (independentProduct rho omega) =
      conditionalMinEntropy rho + conditionalMinEntropy omega ∧
    purificationMaxEntropy (independentProduct rho omega) = purificationMaxEntropy rho + purificationMaxEntropy omega := by sorry

end QAlgorithms.Papers.Independent.Advance50.P12

end
