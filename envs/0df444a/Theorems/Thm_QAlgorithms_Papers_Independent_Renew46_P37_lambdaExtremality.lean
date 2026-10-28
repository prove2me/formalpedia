-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_lambdaExtremality
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.lambdaExtremality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T22:17:43.537564+00:00
-- url     : https://prove2.me/theorems/2356385e-4cbc-4191-9e44-9670b8fe8432
-- title:
--   The exact convex-combination range
-- statement:
--   For real $\lambda$, define $M_n=\lambda S_n+(1-\lambda)T_n$ on normalized finite laws on nonempty local alphabets. If $0\le\lambda\le1$, this is a secrecy monotone for every $n\ge2$. For three parties the converse also holds:
--   $$M_3\text{ is a secrecy monotone}\quad\Longleftrightarrow\quad0\le\lambda\le1.$$
--   Monotonicity refers to local stochastic operations and conditional averages over public messages heard by Eve; the usual positivity, product vanishing, additivity, and fixed-alphabet continuity are included.
--
--   Necessity is not asserted at $n=2$, where the two quantities coincide.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 9, §III.C, (23); §IV.E

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

/-- §III.C, PDF pp.5--6, (23), and §IV.E, PDF p.9: convex combinations
suffice for every n≥2; necessity holds for THREE parties only. -/
theorem lambdaExtremality (lambda : ℝ) :
    ((0 ≤ lambda ∧ lambda ≤ 1) → ∀ n : ℕ, 2 ≤ n →
      IsCMonotone (combination lambda : CData n → ℝ)) ∧
    (IsCMonotone (combination lambda : CData 3 → ℝ) ↔
      0 ≤ lambda ∧ lambda ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
