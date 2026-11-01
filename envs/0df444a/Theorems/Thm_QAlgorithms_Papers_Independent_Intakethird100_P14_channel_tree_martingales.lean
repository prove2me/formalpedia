-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_channel_tree_martingales
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.channel_tree_martingales
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:00:38.399059+00:00
-- url     : https://prove2.me/theorems/1124d847-293b-4006-a7cc-005da8f82a23
-- title:
--   Bounded channel-tree root-fidelity and information martingales
-- statement:
--   Let $W$ be a binary-input classical–quantum channel with normalized density outputs. On a probability space, let $B_1,B_2,\ldots$ be independent fair Bernoulli bits. Let $\mathcal F_n=\sigma(B_1,\ldots,B_n)$, with $\mathcal F_0$ trivial. Starting from $W_0=W$, obtain $W_{n+1}$ from $W_n$ by the bad transform when $B_{n+1}=0$ and by the good transform when $B_{n+1}=1$. Equivalently, the first $n$ bits select the split-channel index minus one in binary. Put $F_n=\sqrt{F(W_n)}$ and $I_n=I(W_n)$, with information measured in bits. Then
--
--   $$(F_n,\mathcal F_n)_{n\ge0}\text{ is a bounded supermartingale},\qquad
--   (I_n,\mathcal F_n)_{n\ge0}\text{ is a bounded martingale},$$
--   $$0\le F_n\le1,\qquad0\le I_n\le1\quad\text{pointwise for every }n.$$
--
--   Both processes are integrable and the extended information is finite before conversion to a real process. In Lean the IID hypothesis is expressed equivalently by measurable bits and probability $2^{-n}$ for every length-$n$ prefix cylinder. This is the stochastic form of the actual channel recursion, not a statement about freely supplied bounded processes.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 8, Lemma 11: bounded fidelity supermartingale and information martingale

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 11, PDF p.8: actual tree processes, with the filtration generated
by exactly the first n IID fair bits. The finite-history cylinder law is
equivalent to independence and Bernoulli(1/2) marginals. Corrects the prose
B_n to B_(n+1) after time n and the displayed missing root in the F_n law.
Finiteness, pointwise [0,1] bounds and integrability are conclusions. -/
theorem channel_tree_martingales {I Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W) (B : ℕ → Omega → Bool)
    (hB : ∀ k, Measurable (B k))
    (hfair : ∀ n (h : Fin n → Bool),
      mu {w | ∀ k : Fin n, B k.val w = h k} = (1 / 2 : ℝ≥0∞) ^ n) :
    (∀ n w, symmetricInformation (splitChannel W n (branchIndex B n w)) ≠ ⊤) ∧
    (∀ n w, 0 ≤ fidelityProcess W B n w ∧ fidelityProcess W B n w ≤ 1 ∧
      0 ≤ informationProcess W B n w ∧ informationProcess W B n w ≤ 1) ∧
    (∀ n, Integrable (informationProcess W B n) mu) ∧
    Supermartingale (fidelityProcess W B) (bitFiltration B hB) mu ∧
    Martingale (informationProcess W B) (bitFiltration B hB) mu := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
