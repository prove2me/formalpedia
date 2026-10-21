-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_pureCanonicalDegradability
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.pureCanonicalDegradability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:13:08.9301+00:00
-- url     : https://prove2.me/theorems/ccd3d739-8ad2-4e4d-8a8b-77379dabcf72
-- title:
--   Ordinary degradability of B1 and quantum-limited C
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Let $E$ be the canonical Gaussian CPTP map. If its class is $B_1$, or its class is $C$ with $N=0$ and $\kappa^2\ge1/2$, then
--
--   $$E\text{ is ordinarily degradable}.$$
--
--   Ordinary degradability uses a true pure Stinespring complement and a CPTP recovery on every density. The $C$ gain $\kappa=1$ is excluded by its class definition. The weakly degradable range is retained; purity alone does not imply this result for smaller transmissivity.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 16, §3.2

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

/-- Section 3.2, PDF pp.16-17: ordinary degradability of B1 and pure C in
the weakly degradable range. Purity alone does not remove k^2>=1/2. -/
theorem pureCanonicalDegradability (c : CanonicalClass) (k N : ℝ)
    (hvalid : ValidSourceCanonical c k N) (E : FockMap)
    (hE : IsGaussianChannel E (canonicalData c k N))
    (hregime : c = .B1 ∨ (c = .C ∧ N = 0 ∧ 1 / 2 ≤ k ^ 2)) :
    OrdinarilyDegradable E := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
