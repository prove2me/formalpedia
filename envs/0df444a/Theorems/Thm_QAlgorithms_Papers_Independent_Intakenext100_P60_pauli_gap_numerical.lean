-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_pauli_gap_numerical
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.pauli_gap_numerical
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:02:26.000988+00:00
-- url     : https://prove2.me/theorems/2be51828-17e6-466a-8a3e-bdd7bdf6f5dc
-- title:
--   §8: the explicit p0=1/2, px=py=pz=1/6 example
-- statement:
--   Let $p_0,p_x,p_y,p_z\ge0$ sum to one, with
--   $$p_0+p_z-p_x-p_y\ge |p_0+p_y-p_x-p_z|,\qquad p_0+p_z-p_x-p_y\ge |p_0+p_x-p_y-p_z|.$$
--   In output:environment order on $\mathbb C^2\otimes\mathbb C^4$, put
--   $$u=\sqrt{p_0}|00\rangle+\sqrt{p_x}|1x\rangle+i\sqrt{p_y}|1y\rangle+\sqrt{p_z}|0z\rangle,$$
--   $$v=\sqrt{p_0}|10\rangle+\sqrt{p_x}|0x\rangle-i\sqrt{p_y}|0y\rangle-\sqrt{p_z}|1z\rangle.$$
--   Write $\rho_s=s|u\rangle\langle u|+(1-s)|v\rangle\langle v|$ for $0\le s\le1$, $\rho_T=\rho_{1/2}$, and $h=H_2(p_0+p_z)$, where $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ and $0\log_2 0=0$. Entanglement is measured across the two displayed parties.
--
--   Fix $(p_0,p_x,p_y,p_z)=(1/2,1/6,1/6,1/6)$. The corrected exact calculation gives
--   $$\|\rho_T^\Gamma\|_1=\frac{2+\sqrt{13}}3,\qquad E_D(\rho_T)\le\log_2\frac{2+\sqrt{13}}3<H_2(1/3)=E_c(\rho_T).$$
--   This provides an explicit strict irreversibility example. The source prints $5/3$ for the norm and uses the stray label $\rho_1$ for its cost. The norm is corrected because its own quartic factors as $(z-1/3)^2(z^2-z/3-1/3)$, with negative partial-transpose eigenvalue $(1-\sqrt{13})/12$ twice. The original quotation is preserved in the metadata; round 1 moderation independently verified this minimal correction.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 15, §8: the explicit p0=1/2, px=py=pz=1/6 example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF p.15: fixed example. Printed: ||rho_T^Gamma||_1=5/3 and Ec(rho_1).
Changed: norm=(2+sqrt(13))/3 and label rho_T. Why: the p.14 quartic factors as
(z-1/3)^2(z^2-z/3-1/3), giving negative partial-transpose eigenvalue
(1-sqrt(13))/12 twice. The strict gap survives. Independent moderation is required. -/
theorem pauli_gap_numerical :
    let p : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 6, 1 / 6]
    let rho := pauliMixture p (1 / 2)
    traceNorm (Entanglement.partialTransposeFirst rho) = (2 + Real.sqrt 13) / 3 ∧
    twoWayDistillable rho ≤ Real.logb 2 ((2 + Real.sqrt 13) / 3) ∧
    Real.logb 2 ((2 + Real.sqrt 13) / 3) < binEntropy2 (1 / 3) ∧
    formationCostBits rho = binEntropy2 (1 / 3) ∧ twoWayDistillable rho < formationCostBits rho := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
