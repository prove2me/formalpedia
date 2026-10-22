-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_remarkA_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.remarkA_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:48:03.841794+00:00
-- url     : https://prove2.me/theorems/36733ff6-f8e2-49c2-b205-764be5a04761
-- title:
--   Monotonicity of normalized testing entropy
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional system. For $0\le\epsilon\le\eta\le\operatorname{tr}\rho$,
--
--   $$D_H^\eta(\rho\|\sigma)\le D_H^\epsilon(\rho\|\sigma).$$
--
--   The zero endpoint uses the continuous right extension and support failures keep their extended values. The direction depends on the acceptance-probability normalization in Definition A.1.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 20, Remark A.4

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

/-- Remark A.4 (PDF p.20): non-increasing in epsilon, including zero. -/
theorem remarkA_4 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (e f : ℝ) (he : 0 ≤ e) (hef : e ≤ f)
    (hf : f ≤ rho.trace.re) :
    endpointTestingEntropyBits f rho sigma ≤ endpointTestingEntropyBits e rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
