-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_single_copy_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.single_copy_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:20:13.004222+00:00
-- url     : https://prove2.me/theorems/6d3f1ef1-8cac-4650-8083-7eeee447c79f
-- title:
--   Explicit single-copy PPT channel with fidelity above the distillation threshold
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d\ge1$, $m\ge2$, and let $\rho$ be an NPT density operator. Let $P_{\rm neg}$ be the spectral projector of $\rho^\Gamma$ on its strictly negative eigenvalues, and let $\mathcal N(\rho)$ be the sum of their absolute values. The norm $\|\cdot\|_\infty$ is the operator norm. For
--
--   $$0<\epsilon\le\min\{2,\|P_{\rm neg}^\Gamma\|_\infty^{-1}\},\qquad A=\frac{I-\epsilon P_{\rm neg}^\Gamma}{m},$$
--
--   $A$ satisfies the isotropic admissibility constraints, and its channel $T_A$, defined by the two-coefficient formula with $B=(I-A)/(m^2-1)$, satisfies
--
--   $$\operatorname{tr}(\rho A)=\operatorname{tr}(P_mT_A(\rho))=\frac{1+\epsilon\mathcal N(\rho)}m>\frac1m.$$
--
--   This is the constructive single-copy threshold witness; it does not claim single-copy perfect distillation.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 2, Theorem 1 proof, Eqs. (6)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.2, (6)–(7): the explicit single-copy witness, its admissibility and its
channel fidelity, strictly above 1/m. Negativity reuses the frozen first-party scalar;
first- and second-party partial transposes are full transposes and have equal trace norms.
NPT makes P_neg nonzero and the operator-norm reciprocal in the interval nondegenerate. -/
theorem single_copy_fidelity (d m : ℕ) (hd : 0 < d) (hm : 2 ≤ m)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (hnpt : ¬ (gamma rho).PosSemidef)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hbound : epsilon ≤ min (2 : ℝ) ((specNorm (gamma (negativeProjector rho)))⁻¹)) :
    let A := negativeSpaceWitness rho m epsilon
    RainsFeasibleEffect m A ∧ IsPositiveConjugatePPTChannel (isotropicPreparation m A) ∧
      effectProb A rho = (1 + epsilon * Entanglement.negativity rho) / (m : ℝ) ∧
      effectProb (bellProjector m) (isotropicPreparation m A rho) = (1 + epsilon * Entanglement.negativity rho) / (m : ℝ) ∧
      1 / (m : ℝ) < effectProb (bellProjector m) (isotropicPreparation m A rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
