-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_thermalFullRank
-- name    : QAlgorithms.Papers.Independent.Information100.P08.thermalFullRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:12:50.303582+00:00
-- url     : https://prove2.me/theorems/af3443d7-d934-4b23-b916-d348c6c71703
-- title:
--   Thermal source structure and lack of pure outputs
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. For $\rho^\star=\theta^{1/2,1/10}$, $$\rho^\star_A=I_2/2,\quad\rho^\star_B=\operatorname{diag}(7/10,3/10),\quad\operatorname{spec}(\rho^\star)=\left\{\frac{15+6\sqrt6}{40},\frac{15-6\sqrt6}{40},\frac1{40},\frac9{40}\right\}.$$ All four eigenvalues are positive, so the state is full rank. The channel $\mathcal G_{1/2,1/10}$ is nonunital and every pure input has a mixed output. The eigenvalue multiset is encoded by equality of the characteristic polynomial; no exact regularized rate is claimed.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 46, Thermal source structure and lack of pure outputs

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.46, (10.14)-(10.22): full rank, complete eigenvalue multiset, marginals, nonunitality,
and mixed output for every pure input. Eigenvalues with multiplicity are encoded by charpoly. -/
theorem thermalFullRank :
    let eig : Fin 4 → ℝ := ![(15 + 6 * Real.sqrt 6) / 40,
      (15 - 6 * Real.sqrt 6) / 40, 1 / 40, 9 / 40]
    IsDensityMatrix thermalState ∧ thermalState.PosDef ∧
    traceRight thermalState = maximallyMixed 2 ∧
    traceLeft thermalState = (!![(7 / 10 : ℂ), 0; 0, 3 / 10]) ∧
    thermalState.charpoly = ∏ i : Fin 4, (Polynomial.X - Polynomial.C (eig i : ℂ)) ∧
    (∀ i, 0 < eig i) ∧
    thermalChannel (1 / 2) (1 / 10) 1 ≠ 1 ∧
    (∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsPure rho →
      ¬ IsPure (thermalChannel (1 / 2) (1 / 10) rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
