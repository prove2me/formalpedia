-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_bellDiagonal_onlyPauli
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.bellDiagonal_onlyPauli
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:53:04.661118+00:00
-- url     : https://prove2.me/theorems/8edb6b50-6b73-44d3-afca-5d5952d07bd6
-- title:
--   Bell-diagonal resources yield only Pauli channels
-- statement:
--   Let $w_0,\ldots,w_3\ge0$ sum to one and let $\tau=\sum_k w_k|B_k\rangle\langle B_k|$, with the Bell ordering $(\Phi^+,\Psi^+,\Psi^-,\Phi^-)$. For every conditional stochastic law $p(l\mid k)$, the branch-averaged Bell-measurement protocol with Pauli corrections simulates a channel $E$ for which there is a normalized probability law $v$ satisfying
--
--   $$E(\rho)=\sum_{l=0}^3 v_l\sigma_l\rho\sigma_l^\dagger\quad\text{for every density matrix }\rho.$$
--
--   Here $(\sigma_0,\sigma_1,\sigma_2,\sigma_3)=(I,X,Y,Z)$. Thus arbitrary classical noise cannot turn a Bell-diagonal resource into a non-Pauli channel.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 6, Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.6, Theorem 12: all normalized Bell mixtures and
all conditional stochastic channels, without a doubly-stochastic restriction. -/
theorem bellDiagonal_onlyPauli (w : Fin 4 → ℝ) (hw : FourOutcomeLaw w)
    (p : Fin 4 → Fin 4 → ℝ) (hp : ClassicalTeleportationLaw p) :
    IsPauli (noisyTeleport (teleportationBellMixture w) p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
