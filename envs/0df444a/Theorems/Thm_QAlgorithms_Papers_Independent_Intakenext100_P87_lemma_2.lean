-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_lemma_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.lemma_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:21:24.461927+00:00
-- url     : https://prove2.me/theorems/82dc2baa-48d0-409a-8904-a40c43035014
-- title:
--   Supplementary Note 2, Lemma 2: entropy bounds measured mutual information
-- statement:
--   Let $|\phi\rangle_{AB}$ be a normalized pure state on arbitrary finite-dimensional registers. Let $X$ and $Y$ be arbitrary local generalized measurements, with arbitrary measurable outcome spaces. Let $I(X:Y)$ denote their classical Shannon mutual information in bits, defined as the supremum over finite measurable coarse grainings. If $\rho_A$ and $\rho_B$ are the reduced density operators, then
--
--   $$I(X:Y)\le S(\rho_A),\qquad I(X:Y)\le S(\rho_B).$$
--
--   This bounds measured classical information by either marginal entropy. The supremum takes values in the extended nonnegative reals; the bound proves it finite.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 19, Supplementary Note 2, Lemma 2: entropy bounds measured mutual information

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.19, Supplementary Note 2, Lemma 2: each marginal entropy bounds the
classical mutual information of arbitrary local generalized measurements on a pure state. -/
theorem lemma_2 {A B X Y : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [MeasurableSpace X] [MeasurableSpace Y]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi)
    (P : OperatorPOVM A X) (Q : OperatorPOVM B Y) :
    measuredInfo (pureDensity psi) P Q ≤ ENNReal.ofReal (vnEntropy (traceRight (pureDensity psi))) ∧
    measuredInfo (pureDensity psi) P Q ≤ ENNReal.ofReal (vnEntropy (traceLeft (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
