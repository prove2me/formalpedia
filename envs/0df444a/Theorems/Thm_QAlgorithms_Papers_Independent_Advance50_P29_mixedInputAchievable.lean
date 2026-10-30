-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_mixedInputAchievable
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.mixedInputAchievable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:21:35.034612+00:00
-- url     : https://prove2.me/theorems/233bba83-0f21-4529-9755-8b1b4c360fef
-- title:
--   §7.4, (25): coherent information of the full maximally mixed input is achievable
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. The operational capacity $Q(\mathcal N)$ is the supremum of all real rates $R$ for which one sequence of nonzero codes $C_n\subset Q^{\otimes n}$, one for every positive integer $n$, has $\limsup_n n^{-1}\log_2\dim C_n\ge R$ and $F_e(C_n,\mathcal N^{\otimes n})\to1$. For a state $\rho$, put $I(\rho,\mathcal N)=S(\mathcal N(\rho))-S_e(\rho,\mathcal N)$, where $S$ is von Neumann entropy and $S_e$ is the entropy of the reference/output state after applying $\mathcal N$ to a purification of $\rho$. For every CPTP channel $\mathcal N$,
--
--   $$
--   Q(\mathcal N)\ge I(\pi,\mathcal N),\qquad 0\le R<I(\pi,\mathcal N)\Longrightarrow R\text{ is achievable}.
--   $$
--
--   The full maximally mixed input gives the direct-coding rate. If its coherent information is nonpositive, the strict nonnegative-rate clause is empty while the capacity inequality still applies.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 18, §7.4, (25): coherent information of the full maximally mixed input is achievable

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.15,17–18, (25): all nonnegative rates strictly below the full mixed-input
coherent information are achievable, and capacity dominates it even when it is nonpositive. -/
theorem mixedInputAchievable [Nonempty I] [Nonempty J] (N : Superop I J)
    (hN : IsChannel N) :
    coherentInformation N (mixed I) ≤ limsupCodeCapacity N ∧
    ∀ R : ℝ, 0 ≤ R → R < coherentInformation N (mixed I) → AchievableCodeRate N R := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
