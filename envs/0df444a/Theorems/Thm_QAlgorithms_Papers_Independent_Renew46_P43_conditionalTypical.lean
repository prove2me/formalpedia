-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_conditionalTypical
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.conditionalTypical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:36:28.52049+00:00
-- url     : https://prove2.me/theorems/686ce9b0-1bf6-4f85-9a49-ab64def4be7f
-- title:
--   Lemma II.10: For word of type P and delta>0, conditional Pi has weight≥1−ad/delta²; sandwich exponent −nH(W|P)±Kd sqrt(a)delta sqrt(n); rank be
-- statement:
--   Let finite input and output sizes be $a,d>0$, let $n>0$, and choose fine spectral resolutions. The input word $x^n$ has its actual empirical law $P$; $W_{x^n}=\bigotimes_iW_{x_i}$. In conditional variance bounds, $\delta>0$, $h=H(W\mid P)$ and $c=K_Vd\sqrt a\,\delta\sqrt n$, where $K_V=2\log_2(e)/e$. A shadow $B$ is an effect with state mass at least $\eta$. Exact-type statements use a simultaneous fine basis of the commuting states $\nu,\rho$, and require the indicated projector to be nonzero. Entropy-threshold projectors use finite sums of realizable count types, with arbitrary real threshold $L$; empty infima are $+\infty$ and exponential tails at infinity are zero.
--
--   $$
--   \operatorname{Tr}(W_{x^n}\Pi)\ge1-ad/\delta^2,\quad2^{-nh-c}\Pi\le\Pi W_{x^n}\Pi\le2^{-nh+c}\Pi,\quad(1-ad/\delta^2)2^{nh-c}\le\operatorname{Tr}\Pi\le2^{nh+c},\quad\operatorname{Tr}B\ge(\eta-ad/\delta^2)2^{nh-c}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 29, Lemma II.10

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

/-- Lemma II.10, PDF p.29: every concentration, sandwich, rank and shadow clause.
P is the word's actual empirical distribution, rather than an unconstrained free law. -/
theorem conditionalTypical {a d n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (S : Fin a → FineResolution d) (w : Fin n → Fin a) (delta : ℝ) (hdelta : 0 < delta) :
    let Pi := conditionalVarianceProjector S w delta
    let rho := wordTensor (fun k => (S (w k)).state)
    let h := wordConditionalEntropy S w
    let correction := varianceConstant * d * Real.sqrt a * delta * Real.sqrt n
    effectProb rho Pi ≥ 1 - (a : ℝ) * d / delta^2 ∧
    Below ((exp2 (-n * h - correction) : ℂ) • Pi) (Pi * rho * Pi) ∧
    Below (Pi * rho * Pi) ((exp2 (-n * h + correction) : ℂ) • Pi) ∧
    Pi.trace.re ≤ exp2 (n * h + correction) ∧
    Pi.trace.re ≥ (1 - (a : ℝ) * d / delta^2) * exp2 (n * h - correction) ∧
    ∀ (B : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (eta : ℝ),
      IsShadow rho B eta →
      B.trace.re ≥ (eta - (a : ℝ) * d / delta^2) * exp2 (n * h - correction) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
