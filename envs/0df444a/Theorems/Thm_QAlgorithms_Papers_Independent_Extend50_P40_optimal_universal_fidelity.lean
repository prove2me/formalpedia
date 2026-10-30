-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_optimal_universal_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.optimal_universal_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:02:53.530165+00:00
-- url     : https://prove2.me/theorems/9d9488f0-cab1-46d0-ace3-f19ad7ccafda
-- title:
--   §II.B.1: optimal universal symmetric N→M cloning in dimension d
-- statement:
--   Let $d\ge2$ and $1\le N<M$. Among fixed CPTP maps on the $N$-copy Bose input algebra whose fidelity is the same for every normalized pure input and every output site, the optimal common single-copy fidelity is
--
--   $$
--   F_{N\to M}(d)=\frac NM+\frac{(M-N)(N+1)}{M(N+d)}.
--   $$
--
--   The canonical Werner channel attains this value. Competitor outputs occupy the full tensor space; Bose output support, covariance, and uniqueness are not imposed on competitors.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 9, §II.B.1: optimal universal symmetric N→M cloning in dimension d

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

/-- II.B.1, PDF pp.8–9 Eq.(21): sharp common single-copy fidelity, with unrestricted
full-tensor competitor outputs. Neither global pureFidelity nor a worst-effect error is optimized. -/
theorem optimal_universal_fidelity (d N M : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) (hNM : N < M) :
    (IsBoseInputChannel (canonicalCloner (d := d) hNM.le) ∧
      UniformCloner (canonicalCloner (d := d) hNM.le) (optimalSingle d N M)) ∧
    ∀ (T : CloneMap d N M) (f : ℝ), IsBoseInputChannel T → UniformCloner T f →
      f ≤ optimalSingle d N M := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
