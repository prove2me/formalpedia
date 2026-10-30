-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_unitalAverage
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.unitalAverage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:08:41.963144+00:00
-- url     : https://prove2.me/theorems/4c591365-bdba-475f-b4e1-8a89b5ebc43b
-- title:
--   §6: averaged fidelity for normalized-unital noise
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix any $K$-dimensional seed code $C_0$ and average $C=UC_0$ over normalized Haar measure on the entire unitary group of $Q$; denote this expectation by $[\,\cdot\,]_K$. All displayed Haar integrands are integrable. Let $\mathcal U$ be CPTP with $\mathcal U(\pi)=I_{Q^{\prime}}/D$, and let $r=|\mathcal U|$ be its minimum Kraus length. Then
--
--   $$
--   [F_e(C,\mathcal U)]_K\ge1-\sqrt{\frac{Kr}{D}}.
--   $$
--
--   This precise expectation estimate expresses the random-coding benefit for normalized-unital noise.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 13, §6: averaged fidelity for normalized-unital noise

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

/-- PDF pp.13–14, §6: averaged fidelity for a normalized-unital CPTP channel. -/
theorem unitalAverage [Nonempty I] [Nonempty J] (N : Superop I J)
    (hN : IsChannel N) (hu : NormalizedUnital N) (C : CodeProjection I) :
    Integrable (fun U => recoveredEntanglementFidelity N (rotatedDensity C U))
      (Schur.unitaryHaar (Fintype.card I)) ∧
    1 - Real.sqrt ((C.dimension : ℝ) * operationLength N / (Fintype.card J : ℝ)) ≤
      codeAverage C (recoveredEntanglementFidelity N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
