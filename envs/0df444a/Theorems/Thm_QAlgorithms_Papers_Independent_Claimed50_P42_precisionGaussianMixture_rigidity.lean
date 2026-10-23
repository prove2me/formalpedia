-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P42_precisionGaussianMixture_rigidity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P42.precisionGaussianMixture_rigidity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:04:29.163981+00:00
-- url     : https://prove2.me/theorems/8301b81b-0438-4fff-b219-ee2f89a6fad1
-- title:
--   Rigidity of convex mixtures of classical Gaussian densities
-- statement:
--   Let $n\ge0$ and let $A$ be a real symmetric positive definite $n\times n$ precision matrix. For a positive definite precision $B$ and a mean $b\in\mathbb R^n$, define
--
--   $$
--   G(B,b,x)=\sqrt{\det B}\,(2\pi)^{-n/2}\exp\!\left[-\tfrac12(x-b)^TB(x-b)\right].
--   $$
--
--   Let $\mu$ be a Borel probability measure on such pairs $(B,b)$. Suppose that for every $x\in\mathbb R^n$ the density section is measurable and integrable and the pointwise mixture identity $G(A,0,x)=\int G(B,b,x)\,\mu(dB,db)$ holds. Then
--
--   $$
--   \mu\!\left(\{(B,b):\exists x\in\mathbb R^n,\ x^T(A-B)x>0\}\right)=0.
--   $$
--
--   Thus almost every contributing component has precision $B\succeq A$. This is a restriction on a full density decomposition, rather than a restriction on only its moments. The integral hypotheses make explicit the source’s convention of genuine probability integrals.
-- source:
--   Gaussian Entanglement of Formation, arXiv:quant-ph/0306177v2, PDF p. 7, Lemma 3, Eqs.(A1)–(A3)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P42

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma pureCovariance)

/-- Lemma 3, PDF pp.7–8, Eqs.(A1)–(A3): almost every mixture component
has precision B >= A. The event uses every real direction and its strict
quadratic-form inequality, not equality of just the first two moments.
The proof's rational-direction bookkeeping requires nonzero directions and
positive integer denominators (A8–A11); this does not change the statement.
The dimension-zero case is retained: its bad event is empty. -/
theorem precisionGaussianMixture_rigidity (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (mu : Measure (PrecisionParameters n)) [IsProbabilityMeasure mu]
    (hmixture : IsPrecisionGaussianMixture A mu) :
    mu {p : PrecisionParameters n | ∃ x : Fin n → ℝ,
      0 < dotProduct x ((A - p.val.1).mulVec x)} = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P42

end
