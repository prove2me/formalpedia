-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_commit_amplitude_attack
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.commit_amplitude_attack
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:34:10.220623+00:00
-- url     : https://prove2.me/theorems/fa1616f9-1ee6-407c-89f5-b23fb8822192
-- title:
--   A larger unverified initial amplitude permits arbitrarily high displacement success
-- statement:
--   Suppose Bob uses only the ideal cat-output parity check, with no amplitude test. Fix an agreed positive entangled-state amplitude $a_0$ and a tolerance $\varepsilon>0$. Alice may instead prepare the normalized odd encoding $|\chi_0(a)\rangle$ at some larger real amplitude $a>a_0$, and subsequently shift her retained proof by $\sqrt2d$ in momentum, for some $d>0$. For the fixed ideal balanced interferometer with the stated coherent amplitude convention, such $a,d$ can be chosen so that
--   $$
--   \Pr\bigl(\text{Bob outputs }1\mid
--   B(I\otimes D(id))|\chi_0(a)\rangle\bigr)>1-\varepsilon.
--   $$
--   The token is unchanged during holding. Under the equiprobable desired-bit convention, the corresponding control is one half of this success probability. This is an existence assertion about the displayed strategy, not an upper bound on general cheating. The initial amplitude is chosen at commit; the proof may then be displaced during holding.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 6, III.C: choosing a larger initial amplitude defeats a parity-only amplitude agreement

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6: choosing a larger honest-form initial amplitude and then a proof
displacement makes changing-bit acceptance arbitrarily close to one when Bob
checks only parity. The text's misplaced 'during the commit phase' is read with
the surrounding holding-phase description; no amplitude test is included here. -/
theorem commit_amplitude_attack (agreed : ℝ) (hAgreed : 0 < agreed)
    (eps : ℝ) (hEps : 0 < eps) :
    CoherentRealized ∧ DisplacementRealized ∧ IsBalanced balancedInterferometer ∧
    ∃ (a d : ℝ), agreed < a ∧ 0 < d ∧ ‖commitmentEncoding (a : ℂ) false‖ = 1 ∧
      1 - eps <
        oppositeProbability false (balancedInterferometer (attackedChi (a : ℂ) false (pShift (Real.sqrt 2 * d)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
