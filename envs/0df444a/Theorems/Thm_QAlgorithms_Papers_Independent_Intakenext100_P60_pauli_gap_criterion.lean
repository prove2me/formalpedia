-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_pauli_gap_criterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.pauli_gap_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:00:28.037321+00:00
-- url     : https://prove2.me/theorems/75bded65-49c9-4895-8211-609188bb09cb
-- title:
--   §8, equation (20): a polynomial criterion for the formation–distillation gap
-- statement:
--   Let $p_0,p_x,p_y,p_z\ge0$ sum to one, with
--   $$p_0+p_z-p_x-p_y\ge |p_0+p_y-p_x-p_z|,\qquad p_0+p_z-p_x-p_y\ge |p_0+p_x-p_y-p_z|.$$
--   In output:environment order on $\mathbb C^2\otimes\mathbb C^4$, put
--   $$u=\sqrt{p_0}|00\rangle+\sqrt{p_x}|1x\rangle+i\sqrt{p_y}|1y\rangle+\sqrt{p_z}|0z\rangle,$$
--   $$v=\sqrt{p_0}|10\rangle+\sqrt{p_x}|0x\rangle-i\sqrt{p_y}|0y\rangle-\sqrt{p_z}|1z\rangle.$$
--   Write $\rho_s=s|u\rangle\langle u|+(1-s)|v\rangle\langle v|$ for $0\le s\le1$, $\rho_T=\rho_{1/2}$, and $h=H_2(p_0+p_z)$, where $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ and $0\log_2 0=0$. Entanglement is measured across the two displayed parties.
--
--   Define
--   $$f_p(z)=z^4-z^3+4(p_0p_xp_y+p_0p_xp_z+p_0p_yp_z+p_xp_yp_z)z-16p_0p_xp_yp_z.$$
--   Writing $\Gamma$ for partial transpose on the output qubit and $\|\cdot\|_1$ for trace norm, the source's criterion is the equivalence
--   $$\log_2\|\rho_T^\Gamma\|_1<E_c(\rho_T)\quad\Longleftrightarrow\quad f_p(-(2^h-1)/2)>0.$$
--   For every admissible distribution, $E_D(\rho_T)\le\log_2\|\rho_T^\Gamma\|_1$. Consequently, whenever the polynomial condition holds,
--   $$E_D(\rho_T)\le\log_2\|\rho_T^\Gamma\|_1<E_c(\rho_T).$$
--   The log-negativity bound is the cited input [34]. This criterion includes closed-simplex boundaries and does not assume the source's overbroad auxiliary negative-root claim.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 14, §8, equation (20): a polynomial criterion for the formation–distillation gap

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

/-- PDF pp.14--15, (20): the polynomial condition is equivalent to the strict
log-negativity--cost inequality on the closed simplex. The upper bound on ordinary
distillation is credited to [34], and gives the strict gap when the condition holds.
No universal negative-root assertion is assumed, including at zero weights. -/
theorem pauli_gap_criterion (p : Fin 4 → ℝ) (hp : PauliAdmissible p) :
    (Real.logb 2 (traceNorm (Entanglement.partialTransposeFirst (pauliMixture p (1 / 2)))) <
      formationCostBits (pauliMixture p (1 / 2)) ↔ GapCriterion p) ∧
    twoWayDistillable (pauliMixture p (1 / 2)) ≤
      Real.logb 2 (traceNorm (Entanglement.partialTransposeFirst (pauliMixture p (1 / 2)))) ∧
    (GapCriterion p → twoWayDistillable (pauliMixture p (1 / 2)) <
      formationCostBits (pauliMixture p (1 / 2))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
