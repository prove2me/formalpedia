-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_normalizedProjectionMoment
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.normalizedProjectionMoment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:25:32.684529+00:00
-- url     : https://prove2.me/theorems/b920d95c-dc72-48da-9a18-0002268d17d8
-- title:
--   Appendix B, (31): second moment of a random normalized code projector
-- statement:
--   Let $Q$ and $Q^{\prime}$ be finite complex Hilbert spaces of positive dimensions $M$ and $D$. A density operator is positive semidefinite with trace one. All logarithms and entropies are in bits. Write $\pi=I_Q/M$. For a nonzero code subspace $C\subset Q$ of dimension $K$, let $\pi_C=\Pi_C/K$. Write $F_e(C,\mathcal N)=\max_{\mathcal R}F_e(\pi_C,\mathcal R\circ\mathcal N)$, where $\mathcal R:B(Q^{\prime})\to B(Q)$ ranges over all CPTP recovery maps and state entanglement fidelity is squared and unconditional. Fix any $K$-dimensional seed code $C_0$ and average $C=UC_0$ over normalized Haar measure on the entire unitary group of $Q$; denote this expectation by $[\,\cdot\,]_K$. All displayed Haar integrands are integrable. For any fixed unit vector $|\psi\rangle\in Q$,
--
--   $$
--   [|\langle\psi|\pi_C|\psi\rangle|^2]_K=\frac{1+K^{-1}}{M^2+M}.
--   $$
--
--   This exact normalized-projector moment is independent of the chosen unit vector and seed code.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 20, Appendix B, (31): second moment of a random normalized code projector

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

/-- PDF pp.20–21, (31): exact second moment of a normalized random code projection. -/
theorem normalizedProjectionMoment [Nonempty I] (C : CodeProjection I)
    (psi : EuclideanSpace ℂ I) (hpsi : ‖psi‖ = 1) :
    Integrable (fun U => Complex.normSq ((pureDensity psi * rotatedDensity C U).trace))
      (Schur.unitaryHaar (Fintype.card I)) ∧
    codeAverage C (fun rho => Complex.normSq ((pureDensity psi * rho).trace)) =
      (1 + (C.dimension : ℝ)⁻¹) /
        ((Fintype.card I : ℝ) ^ 2 + (Fintype.card I : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
