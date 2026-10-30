-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_vacuum_monitor_displacement
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.vacuum_monitor_displacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:33:35.700989+00:00
-- url     : https://prove2.me/theorems/f8825b07-b1cb-4b2e-87e8-13dc80c506fd
-- title:
--   Vacuum monitoring penalty for the specified displacement attack
-- statement:
--   Let $A\in\mathbb C\setminus\{0\}$, $b\in\{0,1\}$, and $d\in\mathbb R$. Under the ideal interferometer and the specified proof displacement, the normalized output is
--   $$
--   |\Psi\rangle=D(-id/\sqrt2)|c_b(A)\rangle\otimes|id/\sqrt2\rangle.
--   $$
--   Let $C_{\rm disp}(A,b,d)$ be one half of the probability that the first output has the parity of bit $1-b$. If Bob additionally requires vacuum in the second output, then
--   $$
--   P_{\rm NoP}=e^{-d^2/2},\qquad
--   \frac12\Pr(\text{opposite parity and second-output vacuum})
--   =C_{\rm disp}(A,b,d)e^{-d^2/2}.
--   $$
--   The factorization follows from these product outputs. This is a strategy-specific penalty; the optimal Gaussian attack for the modified verifier is explicitly left open in the source.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 6, III.C: vacuum monitoring penalty for the specified displacement strategy

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

/-- PDF p.6: vacuum-monitoring penalty for this specified independent-output
displacement attack. The product is a HALF-success, not a global optimum for
the modified protocol; the paper explicitly leaves that optimum open. -/
theorem vacuum_monitor_displacement (A : ℂ) (hA : A ≠ 0) (b : Bool) (d : ℝ) :
    CoherentRealized ∧ DisplacementRealized ∧
    ‖displacedOutput A b d‖ = 1 ∧
    vacuumProbability (displacedOutput A b d) = Real.exp (-d ^ 2 / 2) ∧
    vacuumJointProbability b (displacedOutput A b d) / 2 =
      displacementControl A b d * Real.exp (-d ^ 2 / 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
