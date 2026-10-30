-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P24_singleModeLowPhoton
-- name    : QAlgorithms.Papers.Independent.Advance50.P24.singleModeLowPhoton
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:58:49.222177+00:00
-- url     : https://prove2.me/theorems/e79fe431-ee7e-41f6-a428-98561eafd9c8
-- title:
--   Low-photon expansion with both remainder coefficients
-- statement:
--   Fix $1/2<\eta\le1$. The operational single-mode capacity $C_P(\eta,N)$ in nats is finite at every finite $N\ge0$. For $N>0$ define $r_\eta(N)=C_P(\eta,N)-(2\eta-1)N\log(1/N)$ and put $c(x)=x-x\log x$, with $c(0)=0$. Then
--
--   $$C_P(\eta,N)=(2\eta-1)N\log(1/N)+r_\eta(N),\qquad r_\eta(N)=O(N),$$
--
--   $$c(\eta)-c(1-\eta)\le\liminf_{N\downarrow0}\frac{r_\eta(N)}N\le\limsup_{N\downarrow0}\frac{r_\eta(N)}N\le c(2\eta-1).$$
--
--   The right-hand limit is through positive budgets; constants may depend on fixed $\eta$. For $0\le\eta\le1/2$, the separate correct branch is $C_P(\eta,N)=0$. These bounds retain both finite remainder coefficients rather than only the leading equivalent. The printed theorem omits the necessary transmissivity restriction; the correction follows its own bounding argument.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, PDF p. 2, Theorem 2, (21)–(22): low-photon expansion and both remainder bounds

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

/-- Theorem 2, PDF p.2, (21)--(22), corrected to the proof-supported branch.
The printed theorem omits eta>1/2 and is false below that threshold.
The right-hand liminf/limsup are extended-real extrema; the finite coefficient
bounds prevent junk real extrema. Endpoint coefficients use x-x*log x.
For eta<=1/2 the capacity is exactly zero, rather than having a negative leading term. -/
theorem singleModeLowPhoton (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (∀ N : ℝ, 0 ≤ N → singleCapacity eta N ≠ ⊤) ∧
    (1 / 2 < eta →
      Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (singleRemainder eta) (fun N : ℝ => N) ∧
      (linearEntropyCoefficient eta - linearEntropyCoefficient (1 - eta) : EReal) ≤
        Filter.liminf (fun N : ℝ => ((singleRemainder eta N / N : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ∧
      Filter.liminf (fun N : ℝ => ((singleRemainder eta N / N : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤
        Filter.limsup (fun N : ℝ => ((singleRemainder eta N / N : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ∧
      Filter.limsup (fun N : ℝ => ((singleRemainder eta N / N : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤
        (linearEntropyCoefficient (2 * eta - 1) : EReal)) ∧
    (eta ≤ 1 / 2 → ∀ N : ℝ, 0 ≤ N → singleCapacity eta N = 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P24

end
