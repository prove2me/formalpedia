-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureHolevoAdditivity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureHolevoAdditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:27:32.620902+00:00
-- url     : https://prove2.me/theorems/a3493735-4618-4f90-b7fd-6dbd285ff223
-- title:
--   Lemma 4: two-copy Holevo additivity of qubit erasure
-- statement:
--   Let $\epsilon\in[0,1]$ and let $\mathcal N_\epsilon$ be the qubit erasure channel with a single orthogonal output flag. Let $\chi$ be the ordinary one-shot Holevo maximum over arbitrary finite normalized mixed input ensembles, measured in bits. Then
--
--   $$\chi(\mathcal N_\epsilon\otimes\mathcal N_\epsilon)=\chi(\mathcal N_\epsilon)+\chi(\mathcal N_\epsilon)=2(1-\epsilon).$$
--
--   The tensor-product optimization allows entangled two-qubit input states. This is additivity for two copies of the same channel, without an assertion of additivity against a different channel.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 20, Lemma 4: two-copy Holevo additivity of qubit erasure

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 4, PDF p.20: two equal erasure factors; arbitrary entangled block ensembles allowed. -/
theorem erasureHolevoAdditivity (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    channelHolevo (tensorChannel (qubitErasure epsilon) (qubitErasure epsilon)) =
      channelHolevo (qubitErasure epsilon) + channelHolevo (qubitErasure epsilon) ∧
    channelHolevo (tensorChannel (qubitErasure epsilon) (qubitErasure epsilon)) =
      2 * (1 - epsilon) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
