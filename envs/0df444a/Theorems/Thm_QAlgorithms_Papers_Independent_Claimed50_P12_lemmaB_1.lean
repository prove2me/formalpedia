-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:49:37.136543+00:00
-- url     : https://prove2.me/theorems/d1093db3-34c9-4f4c-8b6e-997bd9bd8364
-- title:
--   Generalized Fuchs–van de Graaf upper bound
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional system with $\operatorname{tr}\rho\ge\operatorname{tr}\sigma$. With root fidelity $F$ and generalized trace distance $\Delta(X,Y)=\tfrac12\|X-Y\|_1+\tfrac12|\operatorname{tr}(X-Y)|$,
--
--   $$\Delta(\rho,\sigma)\le\sqrt{(\operatorname{tr}\rho)^2-F(\rho,\sigma)^2}.$$
--
--   Neither operator must have trace one. The trace ordering is essential to this generalized form.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 21, Lemma B.1

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

/-- Lemma B.1, Eq.156 (PDF p.21). Both inputs may be unnormalized. -/
theorem lemmaB_1 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htrace : sigma.trace.re ≤ rho.trace.re) :
    generalizedTraceDistance rho sigma ≤ Real.sqrt (rho.trace.re ^ 2 - rootFidelity rho sigma ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
