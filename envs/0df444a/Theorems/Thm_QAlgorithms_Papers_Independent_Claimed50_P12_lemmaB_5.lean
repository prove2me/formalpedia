-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaB_5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaB_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:52:40.316048+00:00
-- url     : https://prove2.me/theorems/4846e4e5-1b96-4d95-9f48-68bad8f91aa2
-- title:
--   Root fidelity under every quantum channel
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional input system. For every completely positive trace-preserving map $T$ into a nonzero finite-dimensional output system,
--
--   $$F(\rho,\sigma)\le F(T(\rho),T(\sigma)).$$
--
--   The map acts on both arguments. The statement uses arbitrary nonnegative inputs rather than only density operators.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 22, Lemma B.5

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

/-- Lemma B.5, Eq.163 (PDF p.22): monotonicity under every CPTP map. -/
theorem lemmaB_5 {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (T : Superop I J) (hT : IsChannel T) :
    rootFidelity rho sigma ≤ rootFidelity (T rho) (T sigma) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
