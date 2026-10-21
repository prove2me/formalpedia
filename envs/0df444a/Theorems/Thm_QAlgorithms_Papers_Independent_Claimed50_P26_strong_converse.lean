-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_strong_converse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:57:45.720322+00:00
-- url     : https://prove2.me/theorems/515a24de-0970-43dc-aa51-e5cdde574cb5
-- title:
--   Theorem I.1 (Strong converse)
-- statement:
--   Let $\Phi:\mathcal B(H_{\rm in})\to\mathcal B(H_{\rm out})$ be a completely positive trace-preserving map on nonzero finite-dimensional spaces. Assume covariance under continuous unitary representations of a compact group, with irreducible output representation. Assume that some $\beta>1$ satisfies $S_\alpha^{\min}(\Phi^{\otimes n})=nS_\alpha^{\min}(\Phi)$ for every positive integer $n$ and every $1\le\alpha<\beta$. Then
--
--   $$
--   C_\Phi=\bar\chi^*(\Phi),\qquad
--   \forall R>C_\Phi\ \exists c>0\ \exists n_0\ge1\ \forall n\ge n_0:\quad P_{\rm succ}\le2^{-cn}.
--   $$
--
--   The last bound holds for every positive message count $M$ with $\log_2M\ge nR$ and every unassisted code and POVM. The messages are uniform and codewords may be mixed and entangled across all uses. Here $C_\Phi$ is operational capacity, $\bar\chi^*$ is regularized ordinary Holevo information, and $S_\alpha^{\min}$ is minimum output Rényi entropy in bits. The theorem turns local entropy additivity into an operational strong converse.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 5, Theorem I.1 (Strong converse)

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

/-- PDF p.5, Theorem I.1: preserve compact-group covariance, local self-additivity,
ordinary operational capacity, regularized Holevo equality, and uniform code decay. -/
theorem strong_converse {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (Phi : Superop I J) (hPhi : IsChannel Phi)
    (hA : CovariantIrreducible Phi) (hB : LocalEntropyAdditive Phi) :
    ordinaryClassicalCapacity Phi = regularizedChi 1 Phi ∧ UnassistedExponentialConverse Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
