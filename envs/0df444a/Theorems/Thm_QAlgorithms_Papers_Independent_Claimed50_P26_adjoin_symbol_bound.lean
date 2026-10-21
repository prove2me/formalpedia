-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_adjoin_symbol_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.adjoin_symbol_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:03:49.930958+00:00
-- url     : https://prove2.me/theorems/ed0e0aed-9071-41b7-b6c2-6aa50777f168
-- title:
--   Lemma II.8 (adjoining one classical symbol)
-- statement:
--   Let $E=\{p_x,\rho_x\}$ be a finite normalized quantum ensemble, let $\rho_0$ be any density matrix on the same nonzero finite-dimensional quantum space, let $\alpha>1$, and let $0\le\eta\le1$. Enlarge the classical label space by one new orthogonal symbol and form $E'$ with old weights $(1-\eta)p_x$ and new weight $\eta$ attached to $\rho_0$. Let $\chi_\alpha(E)$ be the ensemble Rényi–Holevo information and $\mu(E')$ its normalized Rényi center. Then
--
--   $$
--   \chi_\alpha(E')\ge(1-\eta)\chi_\alpha(E)
--   +\eta D_\alpha(\rho_0\Vert\mu(E')).
--   $$
--
--   The expression uses extended-real multiplication with $0\cdot(+\infty)=0$, so both endpoints are included. The old register embeds into the enlarged register. This controls the change in information when one classical symbol is added.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 8, Lemma II.8 (adjoining one classical symbol)

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

/-- PDF p.8, Lemma II.8: enlarge the classical register to avoid the impossible
old-register orthogonality premise. Additive form avoids infinity subtraction;
EReal multiplication sets zero times infinity to zero at eta=0. -/
theorem adjoin_symbol_bound {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (alpha : ℝ) (ha : 1 < alpha) (e : Ensemble I) (rho : {rho : Matrix I I ℂ // IsDensityMatrix rho})
    (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    let eNew := adjoin e rho.1 rho.2 eta h0 h1
    (((1-eta)*ensembleRenyiInformation alpha e : ℝ) : EReal) +
      (eta : EReal)*petz alpha rho.1 (ensembleRenyiCenter alpha eNew) ≤ (ensembleRenyiInformation alpha eNew : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
