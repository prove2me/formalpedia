-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundSSA
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundSSA
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:37:27.793374+00:00
-- url     : https://prove2.me/theorems/846b9e7c-3322-4362-a28f-03b55a0d00cb
-- title:
--   Strong subadditivity
-- statement:
--   For every density operator $\rho_{ABC}$ on nonzero finite-dimensional systems,
--
--   $$I(A:C|B)_\rho\ge0.$$
--
--   Conditional mutual information is the actual four-entropy expression, in bits, on the state's marginals. This is the finite-system background claim stated in the introduction.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 1, BackgroundSSA

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

/-- Strong subadditivity (PDF pp.1–2), finite-system background claim. -/
theorem backgroundSSA {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) : 0 ≤ cmi rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
