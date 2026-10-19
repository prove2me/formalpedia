-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_rankOneStandardDual
-- name    : QAlgorithms.Papers.Independent.Information100.P21.rankOneStandardDual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:49:08.730167+00:00
-- url     : https://prove2.me/theorems/86489726-eb96-4816-ab51-874375aae04b
-- title:
--   II.5 — Proposition II.5. If ρ is an entangled two-qubit state, the standard dual (Ds ) has an optimal triple (W, P, Q) with
-- statement:
--   For every entangled two-qubit density operator $\rho$, the standard dual has an optimal feasible triple $(W,P,Q)$ satisfying
--   $$\operatorname{rank}W=1.$$
--   Optimality is a conclusion, not a premise about a supplied witness. This gives the rank-one bridge used for equality.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 8, II.5 — Proposition II.5. If ρ is an entangled two-qubit state, the standard dual (Ds ) has an optimal triple (W, P, Q) with

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 8, Proposition II.5. If ρ is an entangled two-qubit state, the standard dual (Ds ) has an optimal triple (W, P, Q) with. -/
theorem rankOneStandardDual (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) (he : ¬ sep rho) :
  ∃ W P Q : Op QQ, optDS rho W P Q ∧ Matrix.rank W=1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
