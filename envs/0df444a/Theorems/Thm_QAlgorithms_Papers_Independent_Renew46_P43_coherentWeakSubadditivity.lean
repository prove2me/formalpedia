-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_coherentWeakSubadditivity
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.coherentWeakSubadditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:47:08.006509+00:00
-- url     : https://prove2.me/theorems/1f479efb-fba1-4f83-8c2f-3f8743caba54
-- title:
--   Lemma IV.5: Ie(rho;phi1*⊗phi2*)≤Ie(rho1;phi1*)+H(rho2).
-- statement:
--   Let $\rho$ be any normalized state on the two full matrix systems $A_1\otimes A_2$, with marginals $\rho_1,\rho_2$, and let $\phi_{i,*}$ be local CPTP operations. Coherent information is output entropy minus entropy exchange of a purification of the same input state.
--
--   $$
--   I_e(\rho;\phi_{1,*}\otimes\phi_{2,*})\le I_e(\rho_1;\phi_{1,*})+H(\rho_2).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 48, Lemma IV.5

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

/-- Lemma IV.5, PDF pp.48-50: weak subadditivity. The last term is H(rho2),
not the generally invalid stronger coherent-information term. -/
theorem coherentWeakSubadditivity {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (hrho : IsDensityMatrix rho)
    (T : Superop I I) (U : Superop J J) (hT : IsChannel T) (hU : IsChannel U) :
    coherentInformation (both T U) rho ≤
      coherentInformation T (traceRight rho) + vnEntropy (traceLeft rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
