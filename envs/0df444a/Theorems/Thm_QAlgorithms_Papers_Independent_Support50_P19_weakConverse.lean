-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P19_weakConverse
-- name    : QAlgorithms.Papers.Independent.Support50.P19.weakConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:24:26.056677+00:00
-- url     : https://prove2.me/theorems/ed052c9b-42c3-4763-b363-6719e9e30a1a
-- title:
--   Weak converse with binary entropy
-- statement:
--   Let $\mathcal N:A\to B$ be a finite-dimensional channel, $n\ge1$ and $M\ge1$ integers, and let a uniform-message unassisted block code have average success $p_{\rm succ}$ and actual rate $R=\log_2M/n$. If $1-p_{\rm succ}\le\varepsilon$, $0\le\varepsilon<1$, and $\varepsilon\le1-1/M$, then
--   $$R\le\frac{\chi(\mathcal N^{\otimes n})+h_2(\varepsilon)}{n(1-\varepsilon)},\qquad h_2(t)=-t\log_2t-(1-t)\log_2(1-t).$$
--   Here $\chi$ is the single-letter Holevo information of the entire block channel, and $0\log_2 0=0$. The bound applies to arbitrary mixed block codewords and joint POVMs, and gives the usual weak converse.
-- source:
--   Strong converse for the classical capacity of entanglement-breaking and Hadamard channels via a sandwiched Renyi relative entropy, arXiv:1306.1586v4, PDF p. 11, remark3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Support50.P19

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)

open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)

open QAlgorithms.Papers.Independent.Information100.P56 (sandwichedTrace)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess ordinaryClassicalCapacity IsEB IsHadamard)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Claimed50.P26
  (CovariantIrreducible minOutput UnassistedExponentialConverse)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/-- PDF p.11, Remark 3: weak converse for an allowed error bound, with the p.10 convention. -/
theorem weakConverse [Nonempty I] [Nonempty J] (N : Superop I J) (hN : IsChannel N)
    (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (C : UACode (Fin n → I) (Fin n → J) M)
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1) (heM : e ≤ 1 - 1 / (M : ℝ))
    (herr : 1 - uaCodeSuccess (channelPower N n) C ≤ e) :
    (Real.logb 2 (M : ℝ) / (n : ℝ)) ≤ ((QAlgorithms.Papers.Independent.Claimed50.P26.channelChi 1 (channelPower N n)) + binEntropy2 e) / ((n : ℝ) * (1 - e)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P19

end
