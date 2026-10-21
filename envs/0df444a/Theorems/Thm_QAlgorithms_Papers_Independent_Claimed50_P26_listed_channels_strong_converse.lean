-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_listed_channels_strong_converse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.listed_channels_strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:56:32.02419+00:00
-- url     : https://prove2.me/theorems/38492669-6cc5-4c42-96c1-1a7cbc18f073
-- title:
--   Main result: exponential unassisted strong converse for the listed channel classes
-- statement:
--   Let $\Phi$ be a finite-dimensional channel in one of the following classes: a unital qubit channel; the $d$-dimensional depolarizing channel $\Delta_r(X)=rX+(1-r)\operatorname{Tr}(X)I/d$, where $d\ge2$ and $-1/(d^2-1)\le r\le1$; or the Werner–Holevo channel $W_d(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$, where $d\ge2$. Let $C_\Phi$ be its ordinary unassisted classical capacity in bits per use. For every fixed $R>C_\Phi$, there exist $c>0$ and an integer $n_0\ge1$ such that, for every $n\ge n_0$, every positive integer $M$ with $\log_2 M\ge nR$, and every unassisted $M$-message code and decoding POVM,
--
--   $$
--   P_{\rm succ}\le 2^{-cn}.
--   $$
--
--   Messages are uniform. Codewords may be mixed and arbitrarily entangled across the $n$ memoryless uses. The constants may depend on the channel and the fixed rate, and precede all block lengths and code choices. This gives a sharp exponential upper bound above ordinary capacity.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 1, Main result: exponential unassisted strong converse for the listed channel classes

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

/-- PDF pp.1,2,5, main result: all three named classes have an unassisted
exponential strong converse. The unassistedCodingExponent depends on the fixed supercapacity rate;
the stronger rate-uniform gamma suggested by p.2 is not asserted. -/
theorem listed_channels_strong_converse {d : ℕ} (hd : 0 < d)
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) (hclass : ListedChannel Phi) :
    UnassistedExponentialConverse Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
