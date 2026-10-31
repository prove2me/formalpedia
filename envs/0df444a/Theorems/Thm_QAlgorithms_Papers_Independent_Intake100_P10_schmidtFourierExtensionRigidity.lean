-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_schmidtFourierExtensionRigidity
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.schmidtFourierExtensionRigidity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:07:45.230033+00:00
-- url     : https://prove2.me/theorems/2ea8b2ce-e145-45c8-b6c7-3dfe69265e4a
-- title:
--   Every Schmidt/Fourier extension has a common product Eve state
-- statement:
--   Let $d\ge1$ and let $\alpha_0,\ldots,\alpha_{d-1}\in\mathbb C$ satisfy $\sum_j|\alpha_j|^2=1$ and $\alpha_j\ne0$ for every $j$. These coefficients construct $|\phi\rangle=\sum_j\alpha_j|j\rangle_A|j\rangle_B$. Alice measures either the Schmidt basis ($x=0$) or its Fourier conjugate basis $|\widetilde a\rangle=d^{-1/2}\sum_k e^{2\pi iak/d}|k\rangle$ ($x=1$). Thus Bob’s blocks are
--
--   $$\hat\rho_B^{a,0}=|\alpha_a|^2|a\rangle\langle a|,\qquad\hat\rho_B^{a,1}=\frac1d|v_a\rangle\langle v_a|,\qquad |v_a\rangle=\sum_k\alpha_k e^{-2\pi iak/d}|k\rangle.$$
--
--   Let $E$ be any quantum system and let $\hat\tau_{BE}^{a,x}$ be any positive trace-class extension satisfying $\operatorname{Tr}_E\hat\tau_{BE}^{a,x}=\hat\rho_B^{a,x}$ for every $a,x$ and $\sum_a\hat\tau_{BE}^{a,x}$ independent of $x$. Then there exists one positive trace-one state $\omega_E$, chosen before all $a,x$, such that
--
--   $$\hat\tau_{BE}^{a,x}=\hat\rho_B^{a,x}\otimes\omega_E\qquad\text{for every }a,x.$$
--
--   This is rigidity against every no-signaling extension, with no product-extension hypothesis and no bound on Eve’s dimension.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 6, Unnumbered rigidity, (53)–(63)

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

/-- Unnumbered Schmidt/Fourier rigidity, PDF p.6, (53)--(63): all normalized
nonzero coefficients, including d=1. No invertibility on an enlarged Bob space
is assumed. Printed (60) applies only to k=1,...,d-1; k=0 is (59). -/
theorem schmidtFourierExtensionRigidity {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℂ)
    (hnorm : ∑ j, Complex.normSq (alpha j) = 1) (hnonzero : ∀ j, alpha j ≠ 0)
    (E : Type) (r : Extension (schmidtFourierAssemblage alpha) E) :
    ∃ omega : State E, ∀ x a,
      r.block x a = productCoeff (schmidtFourierAssemblage alpha x a) omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
