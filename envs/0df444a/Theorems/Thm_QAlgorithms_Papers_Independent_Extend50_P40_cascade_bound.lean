-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_cascade_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.cascade_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:14:12.981384+00:00
-- url     : https://prove2.me/theorems/fba77fdf-26be-4e8a-b8e8-59eeffde5dda
-- title:
--   §II.E Eqs.(46)–(49): composition and estimation bound
-- statement:
--   Let $1\le N<M<L$. Take CPTP Bose-input, Bose-output qubit cloners $T:N\to M$ and $S:M\to L$ with all-operator radial coefficients $\eta_T,\eta_S$. Their composition has radial coefficient $\eta_S\eta_T$, including on correlated intermediate states, and
--
--   $$
--   \eta_T\frac{M}{M+2}\le\frac{N}{N+2},\qquad\eta_T\le\frac{N}{M}\frac{M+2}{N+2}.
--   $$
--
--   The coefficient rule uses the entire Bose operator algebra; no positive mixture or separability assertion is made for intermediate states.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 14, §II.E Eqs.(46)–(49): composition and estimation bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.E, PDF p.14 Eqs.(46)–(49): coefficient composition on the whole Bose
operator space, followed by the state-estimation bound. No separability is assumed. -/
theorem cascade_bound (N M L : ℕ) (hN : 1 ≤ N) (hNM : N < M) (hML : M < L)
    (T : CloneMap 2 N M) (S : CloneMap 2 M L) (gT gS : ℝ)
    (hT : IsBoseInputChannel T) (hS : IsBoseInputChannel S)
    (hBT : HasBoseOutput T) (hBS : HasBoseOutput S)
    (hgT : HasBlackCowCoefficient hN (by omega) T gT)
    (hgS : HasBlackCowCoefficient (by omega) (by omega) S gS) :
    HasBlackCowCoefficient hN (by omega) (S ∘ T) (gS * gT) ∧
    gT * estimationShrink M ≤ estimationShrink N ∧
    gT ≤ (N : ℝ) / M * (((M : ℝ) + 2) / (N + 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
