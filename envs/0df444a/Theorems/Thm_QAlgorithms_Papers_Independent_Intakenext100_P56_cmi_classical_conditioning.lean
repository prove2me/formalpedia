-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_cmi_classical_conditioning
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.cmi_classical_conditioning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:59:14.62283+00:00
-- url     : https://prove2.me/theorems/7f593f20-b9e7-480a-b8c5-cb17b33e6079
-- title:
--   Lemma 31
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $p_x$ be a finite law and $\rho^x_{ABC}$ be states. For $\rho_{ABCX}=\sum_xp_x\rho^x_{ABC}\otimes|x\rangle\langle x|_X$ and $\alpha>0$, $\alpha\ne1$,
--
--   $$I_\alpha(A;B|CX)_\rho=\frac{\alpha}{\alpha-1}\log\sum_xp_x\exp\!\left(\frac{\alpha-1}{\alpha}I_\alpha(A;B|C)_{\rho^x}\right).$$
--
--   At the continuous endpoint, $I_1(A;B|CX)_\rho=\sum_xp_xI_1(A;B|C)_{\rho^x}$. The exponential uses base $e$, as required by the paper's natural logarithms. The identity describes classical conditioning.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 33, Lemma 31

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

open scoped Matrix.Norms.L2Operator

/-- arXiv:1410.1443v3, PDF pp.33–34, Lemma 31, (A.12).
The removable one endpoint is stated separately, never by totalized division. -/
theorem cmi_classical_conditioning (a : ℝ) (ha : 0 < a)
    (p : X → ℝ) (hp : IsLaw p) (rho : X → Op (A × (B × C)))
    (hrho : ∀ x, IsDensityMatrix (rho x)) :
    (a ≠ 1 → renyiCMI a (conditionedFlag p rho) =
      a/(a-1) * Real.log (∑ x, p x * Real.exp ((a-1)/a * renyiCMI a (rho x)))) ∧
    renyiCMI 1 (conditionedFlag p rho) = ∑ x, p x * renyiCMI 1 (rho x) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
