-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_finite_block_bound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.finite_block_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:10:18.810092+00:00
-- url     : https://prove2.me/theorems/8e5d5d3c-6b69-43b8-bd24-af254df31d3b
-- title:
--   Unnumbered finite-block bound in the proof of Lemma I.2
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving map between nonzero finite-dimensional spaces, let $\alpha>1$, and let $n\ge0$ and $M\ge1$ be integers. For any unassisted code with arbitrary density codewords across $n$ memoryless channel uses and any decoding POVM, the average success for uniform messages satisfies
--
--   $$
--   P_{\rm succ}\le
--   2^{-\frac{\alpha-1}{\alpha}\left(\log_2 M-\chi_\alpha^*(\Phi^{\otimes n})\right)}.
--   $$
--
--   Here $\chi_\alpha^*$ optimizes over all finite normalized input ensembles, and $\Phi^{\otimes0}$ is the scalar channel. For $M=2^{nR}$ this is the source formula with $\log_2M=nR$. The bound is uniform over all codes at each block length, before taking any asymptotic limit.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 9, Unnumbered finite-block bound in the proof of Lemma I.2

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

/-- PDF p.9, proof of I.2: finite-block bound, uniform over arbitrary entangled
mixed-state codewords and decoders. Valid also for the scalar zero-fold channel. -/
theorem finite_block_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (Phi : Superop I J) (hPhi : IsChannel Phi) (alpha : ℝ) (ha : 1 < alpha)
    (n M : ℕ) (hM : 0 < M) (K : UACode (Fin n → I) (Fin n → J) M) :
    uaCodeSuccess (channelPower Phi n) K ≤ Real.rpow 2
      (-((alpha-1)/alpha)*(Real.logb 2 M-channelChi alpha (channelPower Phi n))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
