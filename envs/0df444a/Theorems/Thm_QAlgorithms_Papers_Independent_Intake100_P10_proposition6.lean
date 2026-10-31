-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition6
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:54:38.677363+00:00
-- url     : https://prove2.me/theorems/ee45068f-37c9-4845-8d42-007661f98822
-- title:
--   Schmidt/Fourier steerability equals Schmidt entropy
-- statement:
--   Let $d\ge1$ and let $\alpha_0,\ldots,\alpha_{d-1}\in\mathbb C$ satisfy $\sum_j|\alpha_j|^2=1$ and $\alpha_j\ne0$ for every $j$. These coefficients construct $|\phi\rangle=\sum_j\alpha_j|j\rangle_A|j\rangle_B$. Alice measures either the Schmidt basis ($x=0$) or its Fourier conjugate basis $|\widetilde a\rangle=d^{-1/2}\sum_k e^{2\pi iak/d}|k\rangle$ ($x=1$). Thus Bob’s blocks are
--
--   $$\hat\rho_B^{a,0}=|\alpha_a|^2|a\rangle\langle a|,\qquad\hat\rho_B^{a,1}=\frac1d|v_a\rangle\langle v_a|,\qquad |v_a\rangle=\sum_k\alpha_k e^{-2\pi iak/d}|k\rangle.$$
--
--   The restricted intrinsic steerability, in bits, is
--
--   $$S^R(\hat\rho)=-\sum_j|\alpha_j|^2\log_2|\alpha_j|^2=H(A)_\phi.$$
--
--   If additionally $\alpha_j=1/\sqrt d$ for all $j$, then $S(\hat\rho)=\log_2 d$. This gives an exact evaluation for the constructed assemblage. The case $d=1$ is included and has value zero.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 5, Proposition 6, (45)–(70)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Proposition 6, PDF pp.5--7, (45)--(70): normalized nonzero Schmidt
coefficients; d=1 is included. No unrestricted equality is claimed for a general
nonuniform Schmidt vector. -/
theorem proposition6 {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℂ)
    (hnorm : ∑ j, Complex.normSq (alpha j) = 1) (hnonzero : ∀ j, alpha j ≠ 0) :
    restrictedSteerability (schmidtFourierAssemblage alpha) = ENNReal.ofReal (schmidtEntropyBits alpha) ∧
      ((∀ j, alpha j = 1 / (Real.sqrt (d : ℝ) : ℂ)) →
        intrinsicSteerability (schmidtFourierAssemblage alpha) = ENNReal.ofReal (Real.logb 2 d)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
