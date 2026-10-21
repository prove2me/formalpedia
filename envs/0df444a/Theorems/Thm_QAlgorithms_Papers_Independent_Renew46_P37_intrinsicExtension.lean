-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_intrinsicExtension
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.intrinsicExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:12:49.69787+00:00
-- url     : https://prove2.me/theorems/ee144a6b-c0e8-4142-abd4-6908bb2f7990
-- title:
--   Intrinsic extension over all finite Eve channels
-- statement:
--   Let $M$ be a finite-alphabet $n$-party secrecy monotone as in the conditional-extension result, with $n\ge2$. For every normalized finite joint law $P_{AE}$, set
--   $$M_\downarrow(P_{AE})=\inf_{f\ge1,\,K:E\to\{1,\ldots,f\}}\ \sum_{z:p_K(z)>0}p_K(z)M(P_{A\mid z}),$$
--   where $K$ ranges over all stochastic channels and $p_K$ is the law after processing Eve alone. The infimum is attained at some finite output alphabet and stochastic channel. The value is nonnegative and vanishes on products conditional on Eve. Honest local operations/public messages decrease it on average; Eve's local stochastic processing and Eve's public announcements increase it (public announcements in conditional average).
--
--   This is the finite-alphabet meaning of the printed minimum. No output-cardinality cap and no additivity of the minimized extension are asserted.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 4, §II.B.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

/-- §II.B.2, PDF p.4: minimizing over ALL stochastic Eve channels yields
honest/Eve monotonicity. The finite-alphabet printed minimum is attained;
no cardinality cap or additivity of the minimized extension is assumed. -/
theorem intrinsicExtension {n : ℕ} (hn : 2 ≤ n) (M : CData n → ℝ)
    (hM : IsCMonotone M) :
    ExtensionMonotonicity (intrinsicExtensionValue M) ∧
    (∀ p : EData n, EValid p →
      0 ≤ intrinsicExtensionValue M p ∧
      (ConditionalProduct p → intrinsicExtensionValue M p = 0) ∧
      (∃ f : ℕ, 0 < f ∧ ∃ K : Fin p.eve → Fin f → ℝ,
        IsStochastic K ∧ intrinsicExtensionValue M p = conditionalAverage M (processE p K))) ∧
    (∀ (p : EData n) (f : ℕ) (K : Fin p.eve → Fin f → ℝ),
      EValid p → 0 < f → IsStochastic K →
      intrinsicExtensionValue M p ≤ intrinsicExtensionValue M (processE p K)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
