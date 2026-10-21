-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_ddComposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.ddComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:14:13.867987+00:00
-- url     : https://prove2.me/theorems/3432d5ec-a10b-4e09-af82-fead0b5d0041
-- title:
--   Two class-D channels and their zero capacity
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Here $Q$ denotes unrestricted, unassisted memoryless quantum capacity, defined by arbitrary trace-class CPTP encoders and decoders and entanglement-transmission fidelity tending to one; no energy constraint or Gaussian coding restriction is imposed. Let $E_j$ have class-$D$ data with $\kappa_j>0$ and $N_j\ge0$, $j=1,2$. Their composition $E_{21}=E_2\circ E_1$ is Gaussian, has zero quantum capacity, and has data
--
--   $$K=\kappa_1\kappa_2 I,\quad m=0,\quad\alpha=\bigl[\kappa_2^2(\kappa_1^2+1)(N_1+\tfrac12)+(\kappa_2^2+1)(N_2+\tfrac12)\bigr]I.$$
--
--   If $\kappa_1\kappa_2
--   e1$, it is class $C$ with nonnegative photon parameter
--
--   $$N_0=\frac{(\kappa_2^2+1)N_2+\kappa_2^2(\kappa_1^2+1)N_1}{|\kappa_1^2\kappa_2^2-1|}+\frac12\left(\frac{\kappa_1^2\kappa_2^2+2\kappa_2^2+1}{|\kappa_1^2\kappa_2^2-1|}-1\right).$$
--
--   At product one it is $B_2$ with noise equal to the undivided scalar coefficient of $\alpha$ above. This retains the missing product-one branch while stating the source capacity conclusion.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 18, §4.1; (4.1)–(4.2)

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

/-- Equations (4.1)-(4.2), PDF p.18: two D factors give zero capacity.
Printed unconditional class C is corrected at k1*k2=1 to class B2; undivided
noise is retained there. The outer 1/2 in (4.2) multiplies the entire bracket. -/
theorem ddComposition (k1 k2 N1 N2 : ℝ)
    (h1 : ValidSourceCanonical .D k1 N1) (h2 : ValidSourceCanonical .D k2 N2)
    (E1 E2 : FockMap) (hE1 : IsGaussianChannel E1 (canonicalData .D k1 N1))
    (hE2 : IsGaussianChannel E2 (canonicalData .D k2 N2)) :
    IsGaussianChannel (E2 ∘ E1)
      ⟨(k1 * k2) • 1,
        ((k2 ^ 2 * (k1 ^ 2 + 1) * (N1 + 1 / 2) +
          (k2 ^ 2 + 1) * (N2 + 1 / 2))) • 1, 0⟩ ∧
    operationalTraceClassCapacity (E2 ∘ E1) = 0 ∧
    (k1 * k2 ≠ 1 →
      0 ≤ ddPhotonNumber k1 k2 N1 N2 ∧
      IsGaussianChannel (E2 ∘ E1) (canonicalData .C (k1 * k2) (ddPhotonNumber k1 k2 N1 N2))) ∧
    (k1 * k2 = 1 → IsGaussianChannel (E2 ∘ E1)
      (canonicalData .B2 0 (k2 ^ 2 * (k1 ^ 2 + 1) * (N1 + 1 / 2) +
        (k2 ^ 2 + 1) * (N2 + 1 / 2)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
