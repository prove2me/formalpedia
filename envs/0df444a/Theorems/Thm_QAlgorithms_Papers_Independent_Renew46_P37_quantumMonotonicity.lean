-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P37_quantumMonotonicity
-- name    : QAlgorithms.Papers.Independent.Renew46.P37.quantumMonotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:26:36.655674+00:00
-- url     : https://prove2.me/theorems/b9e65185-d082-4956-acfd-375496732208
-- title:
--   Average monotonicity under complete local instruments
-- statement:
--   Let $\rho$ be a normalized $n$-party density matrix, $n\ge2$, on labelled local Hilbert spaces of nonzero finite dimensions. Let an arbitrary party apply a complete local instrument with arbitrary finite Kraus multiplicities, public outcomes $j$, probabilities $p_j$, and normalized conditional states $\rho_j$; dimensions at that party may change. Then
--   $$\sum_jp_j S_n(\rho_j)\le S_n(\rho),\qquad\sum_jp_j T_n(\rho_j)\le T_n(\rho).$$
--   The subnormalized Kraus equations handle zero-weight branches without dividing by zero. One-outcome instruments include all deterministic CPTP local maps. Every public outcome is heard by Eve.
--
--   These are initial-to-average inequalities, not concavity claims for arbitrary mixtures.
-- source:
--   Multipartite Classical and Quantum Secrecy Monotones, arXiv:quant-ph/0202103v1, PDF p. 10, §V.C, (54)–(65)

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

/-- §V.C, PDF pp.10--11, (54)--(65): arbitrary complete local instruments
can only decrease S_n and T_n on average. One-outcome instruments include all
deterministic dimension-changing CPTP maps. Outcomes retain the full transcript. -/
theorem quantumMonotonicity {n : ℕ} (hn : 2 ≤ n) :
    ∀ (s : FiniteState n) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → FiniteState n),
      LocalInstrument s w r → ∀ kind : InformationKind,
      (∑ j, w j * qValue kind (r j)) ≤ qValue kind s := by sorry

end QAlgorithms.Papers.Independent.Renew46.P37

end
