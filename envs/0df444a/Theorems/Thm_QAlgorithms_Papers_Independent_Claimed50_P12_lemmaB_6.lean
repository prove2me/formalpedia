-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_6
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:53:27.723524+00:00
-- url     : https://prove2.me/theorems/ec33e781-36bb-499e-af33-4ba64d9ffc10
-- title:
--   Transfer of an arbitrary operator between fidelity arguments
-- statement:
--   For nonnegative operators $\rho,\sigma$ and any operator $W$ on the same nonzero finite-dimensional system,
--
--   $$F(\rho,W\sigma W^\dagger)=F(W^\dagger\rho W,\sigma).$$
--
--   No positivity, contractivity or unitarity condition is imposed on $W$. The adjoints occur on opposite sides in the two congruences.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 22, Lemma B.6

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

/-- Lemma B.6, Eq.164 (PDF p.22): W is an arbitrary operator. -/
theorem lemmaB_6 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma W : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    rootFidelity rho (W * sigma * Wᴴ) = rootFidelity (Wᴴ * rho * W) sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
