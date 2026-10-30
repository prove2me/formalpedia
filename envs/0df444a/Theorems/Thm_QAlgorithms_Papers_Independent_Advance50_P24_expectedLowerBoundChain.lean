-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_expectedLowerBoundChain
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.expectedLowerBoundChain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:04:53.172483+00:00
-- url     : https://prove2.me/theorems/e5a42d13-f6a1-4a0b-846f-34a704c66c82
-- title:
--   Mean instantaneous capacity and second-moment lower-bound chain
-- statement:
--   Let $T$ be a measurable random unitary matrix on a probability space, with fixed finite dimensions: $m\ge1$ Alice modes, $k$ Bob modes, $l$ Eve modes and $m\le k+l$. Let $A=T_{ab}$ be its $k\times m$ Alice-to-Bob block. Let $H$ be the eigenvalue vector of $A^\dagger A$, $D$ its diagonal vector, and $\mu=\operatorname{diag}\mathbb E[A^\dagger A]$. Fix $N\ge0$, define $L^M$ as the optimized sum of the scalar lower bounds, and let $F(H,N)$ be the optimized sum of the single-mode operational capacities over nonnegative allocations of exact total $N$. The instantaneous capacities are finite, all quantities below and the Gram matrix are integrable, and
--
--   $$\mathbb E[F(H,N)]\ge\mathbb E[L^M(H,N)]\ge\mathbb E[L^M(D,N)]\ge L^M(\mu,N).$$
--
--   This is the complete analytic expectation chain. Its left side is the mean instantaneous expression in corrected (45); no identification with an operational temporal fading capacity is asserted.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 5, §V-B, (55)–(57): expectation and second-moment lower-bound chain

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)

open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)

open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, (55)--(57): the substantive analytic chain, whose LEFT side is
mean instantaneous optimized capacity, not an operational fading capacity.
Printed (45) omits a sum; the corrected objective sums all modes, as Theorem 4
and (50)--(53) require. This change supplies the otherwise unbound mode index.
T is an actual measurable random unitary on a probability space, with fixed
rectangular dimensions. Measurability is entrywise, equivalently Borel in finite
dimensions. The expected Gram and its integrability are expressed entrywise,
equivalently to the finite-dimensional matrix expectation. Integrability and
pointwise capacity finiteness are conclusions, so no Bochner-integral or
toReal default can erase content. -/
theorem expectedLowerBoundChain {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {m k l : ℕ} (hm : 0 < m) (hdim : m ≤ k + l)
    (T : Omega → Matrix.unitaryGroup (Fin (k + l)) ℂ)
    (hT : ∀ i j : Fin (k + l), Measurable (fun w =>
      (T w : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) i j))
    (N : ℝ) (hN : 0 ≤ N) :
    let A := fun w => aliceBobBlock hdim (T w : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    let G := fun w => aliceBobGram (A w)
    let H := fun w => gramSpectrum (A w)
    let D := fun w i => ((G w) i i).re
    let mu := fun i => (∫ w, G w i i ∂P).re
    (∀ i j : Fin m, Integrable (fun w => G w i j) P) ∧
    (∀ w, allocatedPrivateSup (H w) N ≠ ⊤) ∧
    Integrable (fun w => (allocatedPrivateSup (H w) N).toReal) P ∧
    Integrable (fun w => parallelLower (H w) N) P ∧
    Integrable (fun w => parallelLower (D w) N) P ∧
    (∫ w, parallelLower (H w) N ∂P) ≤
      ∫ w, (allocatedPrivateSup (H w) N).toReal ∂P ∧
    (∫ w, parallelLower (D w) N ∂P) ≤ ∫ w, parallelLower (H w) N ∂P ∧
    parallelLower mu N ≤ ∫ w, parallelLower (D w) N ∂P := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
