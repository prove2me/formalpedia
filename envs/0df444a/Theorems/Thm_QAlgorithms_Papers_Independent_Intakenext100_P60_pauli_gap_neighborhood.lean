-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P60_pauli_gap_neighborhood
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P60.pauli_gap_neighborhood
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:01:40.447455+00:00
-- url     : https://prove2.me/theorems/73ac92ec-29a3-444e-8e84-1bab0aa653a8
-- title:
--   §8: persistence of the strict gap for nearby mixtures
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
--   Assume the strict condition $f_p(-(2^h-1)/2)>0$.
--
--   There is $\delta>0$, depending on these fixed weights, such that
--   $$0\le s\le1,\quad |s-\tfrac12|<\delta\quad\Longrightarrow\quad E_D(\rho_s)\le\log_2\|\rho_s^\Gamma\|_1<E_c(\rho_s)=h.$$
--   This is persistence of the strict gap along the one-parameter mixture line named in the source.
--
--   Here $E_f$ is the infimum of average pure-state marginal entropy over normalized finite decompositions of the stated density matrix. $E_c$ is the asymptotic EPR preparation rate under deterministic two-way LOCC, and $E_D$ is the corresponding asymptotic distillation rate, in bits per copy. All entropies and logarithms are in bits.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, PDF p. 15, §8: persistence of the strict gap for nearby mixtures

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

/-- PDF p.15: continuity gives a neighborhood within the explicitly named mixture
line, not within the full state space. The preceding strict condition (20) is retained. -/
theorem pauli_gap_neighborhood (p : Fin 4 → ℝ) (hp : PauliAdmissible p)
    (hgap : GapCriterion p) :
    ∃ delta > (0 : ℝ), ∀ s ∈ Set.Icc (0 : ℝ) 1, |s - 1 / 2| < delta →
      twoWayDistillable (pauliMixture p s) ≤
        Real.logb 2 (traceNorm (Entanglement.partialTransposeFirst (pauliMixture p s))) ∧
      Real.logb 2 (traceNorm (Entanglement.partialTransposeFirst (pauliMixture p s))) <
        formationCostBits (pauliMixture p s) ∧
      formationCostBits (pauliMixture p s) = binEntropy2 (p 0 + p 3) ∧
      twoWayDistillable (pauliMixture p s) < formationCostBits (pauliMixture p s) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P60
