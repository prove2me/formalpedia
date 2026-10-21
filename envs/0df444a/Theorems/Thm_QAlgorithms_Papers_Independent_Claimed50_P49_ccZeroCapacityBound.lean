-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_ccZeroCapacityBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.ccZeroCapacityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:16:13.01117+00:00
-- url     : https://prove2.me/theorems/872bcc4b-3e1f-4b5f-94af-d47260783319
-- title:
--   Improved closed zero-capacity region
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Here $Q$ denotes unrestricted, unassisted memoryless quantum capacity, defined by arbitrary trace-class CPTP encoders and decoders and entanglement-transmission fidelity tending to one; no energy constraint or Gaussian coding restriction is imposed. For any canonical class-$C$ Gaussian channel with valid amplitude $\kappa$ and noise photon parameter $N$,
--
--   $$N\ge\frac12\left(\frac{\kappa^2}{|\kappa^2-1|}-1\right)\quad\Longrightarrow\quad Q(E)=0.$$
--
--   The endpoint is included, and the denominator is nonzero on class $C$. At $\kappa^2=1/2$ the threshold is zero. This improves (4.3); the complementary region in Fig.3 is only a region where capacity may be nonzero.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 19, §4.2; (4.6)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equation (4.6), PDF p.19, visually checked: improved closed zero-capacity
region. Fig.3's remaining region only CAN have positive capacity; no positive
capacity assertion is inferred. -/
theorem ccZeroCapacityBound (k N : ℝ) (hvalid : ValidSourceCanonical .C k N)
    (E : FockMap) (hE : IsGaussianChannel E (canonicalData .C k N))
    (hbound : (1 / 2) * (k ^ 2 / |k ^ 2 - 1| - 1) ≤ N) :
    operationalTraceClassCapacity E = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
