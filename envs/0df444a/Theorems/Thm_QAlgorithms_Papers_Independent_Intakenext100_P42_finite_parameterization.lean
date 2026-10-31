-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_finite_parameterization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.finite_parameterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:48:40.14411+00:00
-- url     : https://prove2.me/theorems/e954e4a0-9332-4c99-bc48-014053a21370
-- title:
--   Unnumbered: finite product decomposition and 79 angles
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For positive finite local dimensions $d_A,d_B$, every separable state is a convex combination of at most $(d_A d_B)^2$ projectors onto unit product vectors. For two qubits every separable $\rho$ can be written using 79 angles in $[0,2\pi]$ as
--
--   $$\rho=\sum_{i=1}^{16}p_i^2|u_i\rangle\langle u_i|\otimes|v_i\rangle\langle v_i|,\quad p_i=\sin\phi_{i-1}\prod_{j=i}^{15}\cos\phi_j,\quad\phi_0=\pi/2.$$
--
--   Here $u_i=\cos\alpha_i|0\rangle+\sin\alpha_i e^{\mathrm i\eta_i}|1\rangle$ and $v_i=\cos\beta_i|0\rangle+\sin\beta_i e^{\mathrm i\mu_i}|1\rangle$. There are 15 mixing and 64 local angles; an empty product is one. This is a surjective parameterization and a parameter bound.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 20, Unnumbered: finite product decomposition and 79 angles

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.20–22: at most (d_A d_B)^2 pure products, and an explicit 79-angle
surjection for two qubits. This is a parameter count, not a runtime theorem. -/
theorem finite_parameterization :
    (∀ (I J : Type) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
      (rho : Matrix (I × J) (I × J) ℂ), IsSeparableDensity rho →
        HasPureProductDecomposition rho ((Fintype.card I * Fintype.card J)^2)) ∧
    (∀ rho : Matrix (Bool × Bool) (Bool × Bool) ℂ, IsSeparableDensity rho →
      ∃ a : Fin 79 → ℝ, (∀ i, a i ∈ Set.Icc 0 (2*Real.pi)) ∧ rho = angleState a) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
