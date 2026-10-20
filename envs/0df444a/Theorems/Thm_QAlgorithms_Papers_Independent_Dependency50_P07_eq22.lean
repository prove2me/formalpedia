-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_eq22
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.eq22
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:31:14.413849+00:00
-- url     : https://prove2.me/theorems/b33a6e5d-e897-4bf7-9d30-ad9d6e173b5a
-- title:
--   Relation between common randomness and visible pure-state compression
-- statement:
--   Let $E=\{p(x),|\phi_x\rangle\langle\phi_x|\}$ be a finite ensemble of normalized pure states, and let $\rho_Q=\sum_xp(x)|\phi_x\rangle\langle\phi_x|$. Let $D^*$ be the cq excess trade-off. Define the visible compression variational curve quoted from Hayden–Jozsa–Winter [19] by $Q^*(R)=\min_{U|X:I(U;X)=R}H(Q|U)$ for $0\le R\le H(X)$, and by $Q^*(R)=0$ for $R>H(X)$. Then for every $x\ge0$,
--
--   $$D^*(x)+Q^*(D^*(x)+x)=H(\rho_Q).$$
--
--   This identity relates the finite-ensemble common-randomness optimization to the pure-state compression trade-off, including the saturated regime.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 12, §2, (22): relation to pure-state visible compression trade-off

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF p.12, (22): pure-state visible compression relation, including above saturation.
Qstar is the variational curve quoted from [19]; the relation is this paper's result. -/
theorem eq22 (E : CQData X Q) (hE : E.Valid)
    (hpure : ∀ x, ∃ psi : EuclideanSpace ℂ Q, IsState psi ∧ E.state x = pureDensity psi)
    (r : ℝ) (hr : 0 ≤ r) :
    dStar E r + qStar E (dStar E r + r) = vnEntropy (ensembleMean E) := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
