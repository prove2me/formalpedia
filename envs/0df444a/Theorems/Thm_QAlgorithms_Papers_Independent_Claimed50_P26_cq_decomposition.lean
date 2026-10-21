-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_cq_decomposition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.cq_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:02:18.554339+00:00
-- url     : https://prove2.me/theorems/444e2e91-7f0e-4b08-b38c-237f3e948ee0
-- title:
--   Lemma II.6 (cq divergence decomposition)
-- statement:
--   Let $\alpha>1$ and let $\{p_x,\rho_x\}$ be a finite ensemble of density matrices on a nonzero finite-dimensional quantum space, with $p_x\ge0$ and $\sum_xp_x=1$. Write $\rho_{XQ}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$ and $\rho_X=\sum_xp_x|x\rangle\langle x|$. Construct
--
--   $$
--   \zeta=\Bigl(\sum_xp_x\rho_x^\alpha\Bigr)^{1/\alpha},
--   \qquad \mu=\frac{\zeta}{\operatorname{Tr}\zeta}.
--   $$
--
--   Then $\operatorname{Tr}\zeta>0$, $\mu$ is a density matrix, and every quantum density matrix $\sigma$ satisfies
--
--   $$
--   D_\alpha(\rho_{XQ}\Vert\rho_X\otimes\sigma)
--   =D_\alpha(\rho_{XQ}\Vert\rho_X\otimes\mu)+D_\alpha(\mu\Vert\sigma).
--   $$
--
--   The equality is in the extended reals and permits infinite comparison divergence and zero ensemble weights. It isolates all dependence on the comparison state into the second term.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 7, Lemma II.6 (cq divergence decomposition)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF p.7, Lemma II.6: normalization of the constructed ensembleRenyiCenter and the extended
cq decomposition, including zero weights and infinite comparison divergence. -/
theorem cq_decomposition {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (alpha : ℝ) (ha : 1 < alpha) (e : Ensemble I) :
    0 < (ensemblePowerRoot alpha e).trace.re ∧ IsDensityMatrix (ensembleRenyiCenter alpha e) ∧
    ∀ sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho},
      petz alpha (cqState e.prob e.state) (cqComparison e sigma.1) =
        petz alpha (cqState e.prob e.state) (cqComparison e (ensembleRenyiCenter alpha e)) +
          petz alpha (ensembleRenyiCenter alpha e) sigma.1 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
