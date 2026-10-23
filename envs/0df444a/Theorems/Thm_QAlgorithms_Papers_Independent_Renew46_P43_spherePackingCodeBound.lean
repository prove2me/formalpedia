-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_spherePackingCodeBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.spherePackingCodeBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:43:21.200034+00:00
-- url     : https://prove2.me/theorems/6a921e13-d66e-412d-a98e-51a7ed428f2a
-- title:
--   Theorem II.20: For R≥0,delta>0,n≥n0(a,d,delta), constant-composition code with |M|≥2^(n(R+delta)) has e≥(1/2)2^(−nEsp(R,P)(1+delta)).
-- statement:
--   Fix finite input and output sizes $a,d$ and $\delta>0$. A single threshold applies to every normalized channel, every type $P$ and every constant-composition code of that type at nonnegative $R$. Define $E_{\rm sp}(R,P)=\inf_{V:I(P;V)\le R}D(V\Vert W\mid P)$. The code error is maximum message error and an infinite exponent gives zero on the right.
--
--   $$
--   |M|\ge2^{n(R+\delta)}\Longrightarrow e\ge\tfrac12\,2^{-n(1+\delta)E_{\rm sp}(R,P)}\quad(n\ge n_0(a,d,\delta)).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 35, Theorem II.20

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

/-- Theorem II.20, PDF pp.35-36: positive rate slack, maximum error, and one
threshold uniform over channels, types and nonnegative R at fixed a,d,delta. -/
theorem spherePackingCodeBound (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, ∀ (W : FiniteChannel a (fullAlgebra d hd)) (n : ℕ), 0 < n → n0 ≤ n →
      ∀ (P : PMF (Fin a)) (R : ℝ) (c : FiniteCode W n),
      0 ≤ R → c.Composition P → (c.messages : ℝ) ≥ exp2 (n * (R + delta)) →
      c.error ≥ (1/2) * divergenceTail n
        (ENNReal.ofReal (1 + delta) * sphereExponent W R P) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
