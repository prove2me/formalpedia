-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_entropyThresholdBounds
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.entropyThresholdBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:39:15.496827+00:00
-- url     : https://prove2.me/theorems/7ef9f80b-4bc8-4853-b4e1-d251d28cbea5
-- title:
--   Lemma II.14: Conditional entropy-low projector has rank≤(n+1)^(ad)2^(nL), weight≥1−(n+1)^(ad)2^(−n inf_(H(V|P)>L)D(V||W|P)); entropy-high proje
-- statement:
--   Let finite input and output sizes be $a,d>0$, let $n>0$, and choose fine spectral resolutions. The input word $x^n$ has its actual empirical law $P$; $W_{x^n}=\bigotimes_iW_{x_i}$. In conditional variance bounds, $\delta>0$, $h=H(W\mid P)$ and $c=K_Vd\sqrt a\,\delta\sqrt n$, where $K_V=2\log_2(e)/e$. A shadow $B$ is an effect with state mass at least $\eta$. Exact-type statements use a simultaneous fine basis of the commuting states $\nu,\rho$, and require the indicated projector to be nonzero. Entropy-threshold projectors use finite sums of realizable count types, with arbitrary real threshold $L$; empty infima are $+\infty$ and exponential tails at infinity are zero.
--
--   $$
--   \operatorname{Tr}\Pi_{W,H(\cdot\mid P)\le L}^n(x^n)\le(n+1)^{ad}2^{nL},\quad\operatorname{Tr}\bigl(W_{x^n}\Pi_{W,H(\cdot\mid P)\le L}^n(x^n)\bigr)\ge1-(n+1)^{ad}2^{-n\inf_{H(V\mid P)>L}D(V\Vert W\mid P)},\quad\operatorname{Tr}(\rho^{\otimes n}\Pi_{\rho,H(\cdot)\ge L}^n)\ge1-(n+1)^d2^{-n\inf_{H(\nu)\le L}D(\nu\Vert\rho)}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 31, Lemma II.14

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Lemma II.14, PDF p.31: all three inequalities, for arbitrary REAL L. Empty
entropy constraints give +infinity, and all spectral sums range only over realizable types. -/
theorem entropyThresholdBounds {a d n : ℕ} (ha : 0 < a) (hd : 0 < d) (hn : 0 < n)
    (W : FiniteChannel a (fullAlgebra d hd)) (S : Fin a → FineResolution d)
    (hS : ∀ x, (S x).state = W.state x) (rho : FineResolution d)
    (w : Fin n → Fin a) (P : PMF (Fin a))
    (htype : ∀ x, empiricalWeight w x = (P x).toReal) (L : ℝ) :
    (lowConditionalProjector S w L).trace.re ≤ (n+1 : ℝ)^(a*d) * exp2 (n * L) ∧
    effectProb (wordTensor (fun i => W.state (w i))) (lowConditionalProjector S w L) ≥
      1 - (n+1 : ℝ)^(a*d) * divergenceTail n (individualExponent W P L) ∧
    effectProb (copies n rho.state) (highEntropyProjector rho n L) ≥
      1 - (n+1 : ℝ)^d * divergenceTail n (lowEntropyDivergence rho.state L) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
