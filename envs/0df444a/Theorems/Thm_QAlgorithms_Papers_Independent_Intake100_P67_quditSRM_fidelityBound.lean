-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_quditSRM_fidelityBound
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.quditSRM_fidelityBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:24:10.252357+00:00
-- url     : https://prove2.me/theorems/e7933f15-244a-429d-8a12-331010b884d6
-- title:
--   Attainable completed-SRM qudit fidelity bounds
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Use $N$ normalized maximally entangled pairs $|\phi^+\rangle=d^{-1/2}\sum_{a=0}^{d-1}|aa\rangle$ and the completed SRM built from $\sigma_i=d^{-(N-1)}P^+_{A_iC}\otimes I_{\bar A_i}$. Alice reports $i$ and Bob retains $B_i$ without correction. The completed effects are positive and sum to identity, and the resulting map $\Lambda$ is a quantum channel.
--
--   Let $F$ be its entanglement fidelity with the same positive maximally entangled reference and let $f$ be its Haar average pure-input fidelity. Then
--
--   $$F\ge1-\frac{d^2-1}{N},\qquad f=\frac{dF+1}{d+1}\ge1-\frac{d(d-1)}{N}.$$
--
--   These inequalities apply also when their right-hand sides are negative; no additional lower bound on $N$ is imposed.
--
--   The paper credits the bound to [25] and supplies its proof in Appendix B.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 5, §IV A, Eq. (31); Appendix B p.12

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.5–6, Eq.(31), Appendix B p.12: attainable completed-SRM qudit bounds.
The stronger entanglement-fidelity bound is explicit in Appendix B; no N>d^2 assumption. -/
theorem quditSRM_fidelityBound (N d : ℕ) (hN : 1 ≤ N) (hd : 2 ≤ d) :
    IsChannel (quditChannel N d) ∧
    (∀ i, (completedSRM (quditSignal N d) i).PosSemidef) ∧
    (∑ i, completedSRM (quditSignal N d) i) = 1 ∧
    QuditFidelity.entanglementFidelity d (by omega) (quditChannel N d) ≥
      1 - ((d : ℝ) ^ 2 - 1) / N ∧
    QuditFidelity.averageFidelity d (by omega) (quditChannel N d) =
      ((d : ℝ) * QuditFidelity.entanglementFidelity d (by omega) (quditChannel N d) + 1) /
        (d + 1) ∧
    QuditFidelity.averageFidelity d (by omega) (quditChannel N d) ≥
      1 - (d : ℝ) * (d - 1) / N := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
