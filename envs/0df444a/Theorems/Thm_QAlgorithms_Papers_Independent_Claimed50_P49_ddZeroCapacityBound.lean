-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_ddZeroCapacityBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.ddZeroCapacityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:14:47.36414+00:00
-- url     : https://prove2.me/theorems/2c4ee49d-8ecc-4d4e-8a57-0a564ee516cb
-- title:
--   First closed zero-capacity region
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Here $Q$ denotes unrestricted, unassisted memoryless quantum capacity, defined by arbitrary trace-class CPTP encoders and decoders and entanglement-transmission fidelity tending to one; no energy constraint or Gaussian coding restriction is imposed. For a canonical class-$C$ Gaussian channel with amplitude $\kappa$ and noise photon parameter $N$,
--
--   $$N\ge\frac12\left(\frac{\kappa^2+1}{|\kappa^2-1|}-1\right)\quad\Longrightarrow\quad Q(E)=0.$$
--
--   The denominator is nonzero because $\kappa>0$ and $\kappa
--   e1$. This states the closed region of (4.3), without claiming a finite two-$D$ factorization at its boundary.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 19, §4.1; (4.3)

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

/-- Equation (4.3), PDF p.19: closed first zero-capacity region.
No finite DD factorization at equality is asserted: the stronger (4.6) bound
covers the closed boundary without assuming continuity of quantum capacity. -/
theorem ddZeroCapacityBound (k N : ℝ) (hvalid : ValidSourceCanonical .C k N)
    (E : FockMap) (hE : IsGaussianChannel E (canonicalData .C k N))
    (hbound : (1 / 2) * ((k ^ 2 + 1) / |k ^ 2 - 1| - 1) ≤ N) :
    operationalTraceClassCapacity E = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
