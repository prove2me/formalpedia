-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_ccComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.ccComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:15:40.108059+00:00
-- url     : https://prove2.me/theorems/a7585c4e-66cb-4d11-853d-32fa0f7539f9
-- title:
--   C followed by anti-degradable C
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Here $Q$ denotes unrestricted, unassisted memoryless quantum capacity, defined by arbitrary trace-class CPTP encoders and decoders and entanglement-transmission fidelity tending to one; no energy constraint or Gaussian coding restriction is imposed. Let $E_j$ have valid class-$C$ data $(\kappa_j,N_j)$, with $N_j\ge0$, and assume $\kappa_2^2\le1/2$. Then $E_{21}=E_2\circ E_1$ is Gaussian with zero quantum capacity and
--
--   $$K=\kappa_1\kappa_2 I,\quad m=0,\quad\alpha=\bigl[\kappa_2^2|\kappa_1^2-1|(N_1+\tfrac12)+|\kappa_2^2-1|(N_2+\tfrac12)\bigr]I.$$
--
--   If the product amplitude is not one, the nonnegative class-$C$ photon parameter is
--
--   $$N_0=\frac{|\kappa_2^2-1|N_2+\kappa_2^2|\kappa_1^2-1|N_1}{|\kappa_1^2\kappa_2^2-1|}+\frac12\left(\frac{\kappa_2^2|\kappa_1^2-1|+|\kappa_2^2-1|}{|\kappa_1^2\kappa_2^2-1|}-1\right).$$
--
--   At product one it is $B_2$ with the undivided noise coefficient above. Including vacuum factors makes the closed thresholds meaningful.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 19, §4.2; (4.4)–(4.5)

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

/-- Equations (4.4)-(4.5), PDF p.19: C followed by anti-degradable C.
Vacuum inputs Nj=0 are included. The product-one branch is B2, as the source
already states on p.11; (4.5)'s denominator is used only off that branch. -/
theorem ccComposition (k1 k2 N1 N2 : ℝ)
    (h1 : ValidSourceCanonical .C k1 N1) (h2 : ValidSourceCanonical .C k2 N2)
    (hanti : k2 ^ 2 ≤ 1 / 2) (E1 E2 : FockMap)
    (hE1 : IsGaussianChannel E1 (canonicalData .C k1 N1))
    (hE2 : IsGaussianChannel E2 (canonicalData .C k2 N2)) :
    IsGaussianChannel (E2 ∘ E1)
      ⟨(k1 * k2) • 1,
        (k2 ^ 2 * |k1 ^ 2 - 1| * (N1 + 1 / 2) +
          |k2 ^ 2 - 1| * (N2 + 1 / 2)) • 1, 0⟩ ∧
    operationalTraceClassCapacity (E2 ∘ E1) = 0 ∧
    (k1 * k2 ≠ 1 →
      0 ≤ ccPhotonNumber k1 k2 N1 N2 ∧
      IsGaussianChannel (E2 ∘ E1) (canonicalData .C (k1 * k2) (ccPhotonNumber k1 k2 N1 N2))) ∧
    (k1 * k2 = 1 → IsGaussianChannel (E2 ∘ E1)
      (canonicalData .B2 0 (k2 ^ 2 * |k1 ^ 2 - 1| * (N1 + 1 / 2) +
        |k2 ^ 2 - 1| * (N2 + 1 / 2)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
