-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_canonical_single_clone
-- name    : QAlgorithms.Papers.Independent.Support21.P16.canonical_single_clone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:43:51.499125+00:00
-- url     : https://prove2.me/theorems/05d885e9-fb8d-4bb4-a173-34dceaaac61a
-- title:
--   The explicit single-clone coefficient
-- statement:
--   Let $d>0$ and $1\le N<M$ be integers. Let $s_k$ be the Bose projector, $D_k=\binom{d+k-1}{k}$, and $\widehat T_{MN}(A)=(D_N/D_M)s_M((s_NAs_N)\otimes I^{\otimes(M-N)})s_M$. Set
--   $$
--   g_{MN}=\frac{N}{d+N}\frac{d+M}{M}.
--   $$
--   For every Bose-supported operator $A$, its one-site restrictions satisfy $R_M(\widehat T_{MN}(A))=g_{MN}R_N(A)+(1-g_{MN})\operatorname{tr}(A)I/d$. In particular, for every unit $\phi\in\mathbb C^d$ and $\sigma=|\phi\rangle\langle\phi|$,
--   $$
--   \operatorname{Re}\operatorname{tr}\bigl(\sigma R_M(\widehat T_{MN}(\sigma^{\otimes N}))\bigr)
--   =g_{MN}+\frac{1-g_{MN}}{d}.
--   $$
--   This computes the canonical cloner's single-site behavior. It makes no claim of general-$d$ single-clone optimality and does not identify a unique numerical coefficient when $d=1$.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 8, canonical-single-clone

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF pp.7–8 Eq.(3.8): the explicit Black Cow representative and resulting
one-site overlap. No general-d single-clone optimality is asserted. -/
theorem canonical_single_clone (d N M : ℕ) (hd : 0 < d) (hN : 1 ≤ N) (hNM : N < M) :
    HasBlackCowCoefficient hN (by omega) (canonicalCloner (d := d) hNM.le)
      (canonicalCoefficient d N M) ∧
    (∀ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 →
      ((QAlgorithms.pureDensity phi) *
        oneSite (by omega) (canonicalCloner hNM.le
          (QAlgorithms.pureDensity (coherentTensor N phi)))).trace.re =
      canonicalCoefficient d N M + (1 - canonicalCoefficient d N M) / d) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
