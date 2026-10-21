-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P35_ergodicExpectation_and_commutant
-- name    : QAlgorithms.Papers.Independent.Renew46.P35.ergodicExpectation_and_commutant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:07:19.26399+00:00
-- url     : https://prove2.me/theorems/16b690c1-65af-43f2-95ec-0c09e09cbc9d
-- title:
--   Lemma 12: ergodic conditional expectation and Kraus commutant
-- statement:
--   Let $F$ be a CPTP map on the operators of a nonzero finite-dimensional space $H$, with a faithful invariant density $s$. Fix any finite normalized Kraus representation $F(Z)=\sum_iB_iZB_i^*$ and let $F^*$ be its trace adjoint. There exist a unital star subalgebra $\mathcal A$ and a complex-linear conditional expectation $P^*$ onto it such that, for every operator $X$,
--
--   $$P^*(X)=\lim_{N\to\infty}\frac1N\sum_{n=1}^N(F^*)^n(X),\qquad\mathcal A=\{X:F^*(X)=X\}=\{B_i,B_i^*\}' .$$
--
--   The prime denotes the common commutant. The conditional expectation is completely positive, unital and idempotent, has exact range $\mathcal A$, and satisfies $P^*(LXR)=LP^*(X)R$ for $L,R\in\mathcal A$. Convergence is in the finite-dimensional operator space. The faithful invariant state is the Appendix's standing hypothesis.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, PDF p. 8, Lemma 12: ergodic conditional expectation and Kraus commutant

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF p.8, Lemma 12 with the Appendix's faithful invariant state: ergodic expectation and
Kraus commutant. Convergence is asserted, rather than assigned a total default limit. -/
theorem ergodicExpectation_and_commutant {H : Type*} [Fintype H] [Nonempty H]
    (f : Superop H H) (hf : IsChannel f) (s : Matrix H H ℂ)
    (hs : IsDensityMatrix s) (hfaithful : s.PosDef) (hinvariant : f s = s)
    (m : ℕ) (b : Fin m → Matrix H H ℂ) (hb : IsKrausFamily b)
    (hrepresentation : ∀ x, f x = krausApply b x) :
    ∃ a : StarSubalgebra ℂ (Matrix H H ℂ),
    ∃ p : Matrix H H ℂ →ₗ[ℂ] Matrix H H ℂ,
      IsConditionalExpectation p a ∧
      (∀ x, Filter.Tendsto (fun n => dualMean f n x) Filter.atTop (nhds (p x))) ∧
      (∀ x, x ∈ a ↔ traceAdjoint f x = x) ∧
      (∀ x, x ∈ a ↔ ∀ i, x * b i = b i * x ∧ x * (b i)ᴴ = (b i)ᴴ * x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P35

end
