-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_cq_variational
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.cq_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:02:59.220337+00:00
-- url     : https://prove2.me/theorems/d4996201-56f9-4110-ba25-5cf64df94242
-- title:
--   Lemma II.7 (cq variational identity and unique minimizer)
-- statement:
--   For a finite normalized ensemble $\{p_x,\rho_x\}$ on a nonzero finite-dimensional space and an order $\alpha>1$, let $\rho_{XQ}=\sum_xp_x|x\rangle\langle x|\otimes\rho_x$ with classical marginal $\rho_X$. Put $\zeta=(\sum_xp_x\rho_x^\alpha)^{1/\alpha}$, $\mu=\zeta/\operatorname{Tr}\zeta$, and $\chi_\alpha=\alpha\log_2(\operatorname{Tr}\zeta)/(\alpha-1)$. Then $\mu$ is a density matrix and
--
--   $$
--   \chi_\alpha=\min_{\sigma\in\mathcal S(H_Q)}
--   D_\alpha(\rho_{XQ}\Vert\rho_X\otimes\sigma).
--   $$
--
--   The minimum is attained at $\mu$. For every density matrix $\sigma$, the displayed divergence is at least $\chi_\alpha$, with equality if and only if $\sigma=\mu$. Singular comparison states are included. This characterizes the value and unique minimizer of the cq variational problem.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 7, Lemma II.7 (cq variational identity and unique minimizer)

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

/-- PDF p.7, Lemma II.7 (21)–(22): value, attainment at mu, and the unique
minimizer; all density comparison states, including singular ones, are included. -/
theorem cq_variational {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (alpha : ℝ) (ha : 1 < alpha) (e : Ensemble I) :
    (ensembleRenyiInformation alpha e : EReal) =
      (⨅ sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho}, petz alpha (cqState e.prob e.state) (cqComparison e sigma.1)) ∧
    IsDensityMatrix (ensembleRenyiCenter alpha e) ∧
    petz alpha (cqState e.prob e.state) (cqComparison e (ensembleRenyiCenter alpha e)) = (ensembleRenyiInformation alpha e : EReal) ∧
    ∀ sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho}, (ensembleRenyiInformation alpha e : EReal) ≤
      petz alpha (cqState e.prob e.state) (cqComparison e sigma.1) ∧
      (petz alpha (cqState e.prob e.state) (cqComparison e sigma.1) = (ensembleRenyiInformation alpha e : EReal) ↔
        sigma.1 = ensembleRenyiCenter alpha e) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
