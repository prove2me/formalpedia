-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_eq23
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.eq23
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:32:51.705138+00:00
-- url     : https://prove2.me/theorems/95753f5a-5989-44d5-819f-d68c8b4cd53f
-- title:
--   Fixed one-copy measurement common-randomness curve
-- statement:
--   Let $\rho^{AB}$ be a density matrix on finite nonzero systems and $R\ge0$. Let $C^{(1)}(\rho,R)$ optimize the operational rate obtained by repeating one finite POVM $M$ on Alice’s copies, then applying a cq common-randomness protocol. Write $X$ for its outcome and $Q=B$ for Bob’s retained system. Then
--
--   $$C^{(1)}(\rho,R)=R+\max_M\max_{U|X}\{I(U;Q):I(U;X)-I(U;Q)\le R\}.$$
--
--   Both maxima are attained: one pair $(M,U)$ is feasible and dominates every feasible pair, and its auxiliary dominates all feasible auxiliaries for that measurement. This characterizes the fixed-measurement curve before the time sharing discussed on p.18.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 15, §3, (23): the fixed one-copy measurement CR curve

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

/-- PDF p.15, (23): both nested maxima are attained for the operational fixed-POVM curve. -/
theorem eq23 (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (R : ℝ) (hR : 0 ≤ R) :
    fixedCapacity rho R = R + sSup (measurementValues rho R) ∧
    ∃ M : Measurement A, ∃ V : Auxiliary (Fin M.outcomes),
      auxCost (measuredCQ rho M) V ≤ R ∧
      fixedCapacity rho R = R + auxIQ (measuredCQ rho M) V ∧
      (∀ W : Auxiliary (Fin M.outcomes), auxCost (measuredCQ rho M) W ≤ R →
        auxIQ (measuredCQ rho M) W ≤ auxIQ (measuredCQ rho M) V) ∧
      (∀ N : Measurement A, ∀ W : Auxiliary (Fin N.outcomes),
        auxCost (measuredCQ rho N) W ≤ R →
        auxIQ (measuredCQ rho N) W ≤ auxIQ (measuredCQ rho M) V) := by sorry

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
