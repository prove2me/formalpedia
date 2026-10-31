-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P68_bell_point_continuity
-- name    : QAlgorithms.Papers.Independent.Intake100.P68.bell_point_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:13:35.723514+00:00
-- url     : https://prove2.me/theorems/cb62b029-9772-41ab-bf02-bead26673bda
-- title:
--   Unnumbered result: continuity at an EPR state
-- statement:
--   Let $E$ be a finite real-valued functional on finite bipartite asymptotic resource products. Assume only that an actual asymptotic LOCC conversion $R^{\otimes x}\to S^{\otimes y}$, with $x>0$ and $y\ge0$, implies $yE(S)\le xE(R)$. Supplies mean independent integer copy counts with floors; conversion permits every positive error and rate slack, all sufficiently large block lengths, and unconditional normalized output. The same functional is used across positive finite local dimensions. Neither additivity nor continuity is assumed.
--
--   On the fixed two-qubit density space, write $\Phi^+=|\Phi^+\rangle\langle\Phi^+|$ for the normalized positive-sign Bell projector. Then
--
--   $$E\text{ is continuous at }\Phi^+.$$
--
--   Continuity uses trace distance in this fixed space, including the one-sided mixture limits specified by note [10]. No Bell normalization of $E$ is required. The source's later change to the symbol $\Psi^+$ is treated as a locally equivalent Bell-label slip. The cited near-Bell distillation protocol is uniform in the noise density; local Bell twirling extends that argument to arbitrary nearby density operators.
--
--   This statement records the source result at fixed finite dimensions and can be reused with the same operational conversion convention.
-- source:
--   On the continuity of asymptotic measures of entanglement, arXiv:quant-ph/0203107v1, PDF p. 3, Unnumbered result: continuity at an EPR state

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P68

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

/-- PDF p.3, after (25): continuity at the Bell surface point on the
fixed two-qubit density space. The near-Bell distillation protocol is uniform
in its noise state; the Bell fraction of a nearby density also tends to one.
Phi-plus/Psi-plus in the prose is a label slip. No ebit normalization. -/
theorem bell_point_continuity
    (E : SupplyProduct → ℝ) (hE : IsAsymptoticMeasure E) :
    ∀ rho : DensitySpace 2 2, rho.val = phiPlusDensity →
      ContinuousAt (fun sigma : DensitySpace 2 2 => resourceSingleValue E sigma.val) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P68

end
