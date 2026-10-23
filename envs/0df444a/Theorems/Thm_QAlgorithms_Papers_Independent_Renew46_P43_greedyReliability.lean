-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_greedyReliability
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.greedyReliability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:42:33.926276+00:00
-- url     : https://prove2.me/theorems/47b704c2-0c82-4334-a25f-f69f1af2c158
-- title:
--   Corollary II.19: For 0≤R≤C(W): E(R)≥Eg(R)=max_(P:R≤I(P;W))Eg(R,P).
-- statement:
--   For a finite stationary channel $W$, define $E(R)$ by the joint lower limit of $-n^{-1}\log_2 e_{\min}(n,R-\delta)$ as $n\to\infty$ and $\delta\downarrow0$. Zero error has exponent $+\infty$. Let $0\le R\le C(W)$ and use the greedy exponents just defined. The maxima over input laws and the optimizing entropy-threshold pair are attained, as asserted in the source.
--
--   $$
--   E(R)\ge E_g(R)=\max_{P:R\le I(P;W)}E_g(R,P),\qquad0\le R\le C(W).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 35, Corollary II.19

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary II.19, PDF p.35: endpoints and attainment of both printed maxima
are retained; zero-error reliability values may be +infinity. -/
theorem greedyReliability {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (W : FiniteChannel a (fullAlgebra d hd)) (R : ℝ) (hR : 0 ≤ R) (hcap : R ≤ W.capacity) :
    reliability W R ≥ greedyBound W R ∧
    (∃ P : PMF (Fin a), R ≤ W.information P ∧ greedyBound W R = greedyExponent W R P) ∧
    (∀ P : PMF (Fin a), R ≤ W.information P → ∃ L Lprime : ℝ, R ≤ Lprime - L ∧
      greedyExponent W R P =
        min (individualExponent W P L) ((1/2 : ℝ≥0∞) * collectiveExponent W P Lprime)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
