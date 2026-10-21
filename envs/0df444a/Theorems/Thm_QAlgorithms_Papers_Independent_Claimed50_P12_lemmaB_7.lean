-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_7
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:43:56.315679+00:00
-- url     : https://prove2.me/theorems/da773e0e-b62f-4978-89eb-7cd23c5d0bed
-- title:
--   Fidelity bound for a finite resolution of the identity
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space and let $(W_d)_{d\in D}$ be a finite family of operators with $\sum_dW_d=1$. Then, for root fidelity,
--
--   $$\sum_{d\in D}F(W_d^\dagger\rho W_d,\sigma)\ge F(\rho,\sigma).$$
--
--   No positivity, contractivity or projection condition is imposed on the family. This resolution-of-identity estimate is used to select a spectral sector in the recovery proof.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 22, Lemma B.7

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

/-- Lemma B.7, Eq.166 (PDF p.22): sum W_d = identity, not sum W_d†W_d.
No positivity, projection, or contractivity assumptions on the finite family. -/
theorem lemmaB_7 {I D : Type*} [Fintype I] [Fintype D]
    [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (W : D → Op I) (hsum : ∑ d, W d = 1) :
    rootFidelity rho sigma ≤ ∑ d, rootFidelity ((W d)ᴴ * rho * W d) sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
