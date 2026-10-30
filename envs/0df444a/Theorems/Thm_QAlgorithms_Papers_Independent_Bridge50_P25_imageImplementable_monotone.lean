-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_imageImplementable_monotone
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.imageImplementable_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:12:52.44999+00:00
-- url     : https://prove2.me/theorems/78658000-d83d-4946-b6a2-4f8849873ad5
-- title:
--   Theorem A.1: any LOCC monotone on an image-implementable channel
-- statement:
--   Let $E^{A:B}$ be a family of nonnegative real-valued functions on density matrices in every positive finite local dimension, nonincreasing under all finite LOCC, including local addition and disposal. Let $T:M_{d_A}\to M_{d_B}$ be a channel. Suppose a normalized state $\sigma_{A''A'}$, with $d_{A'}=d_A$ and arbitrary positive finite $d_{A''}$, and a two-party LOCC map $\Lambda$ implement $T$ by
--
--   $$T(\rho_A)=\Lambda\!\left(\rho_A\otimes(\mathrm{id}_{A''}\otimes T)(\sigma_{A''A'})\right)$$
--
--   for every input density matrix $\rho_A$, across the split $AA'':B'$, with Alice discarded at the output. Define $E(T)=\sup_{R,\rho_{RA}}E^{R:B}((\mathrm{id}_R\otimes T)(\rho_{RA}))$, allowing an infinite supremum. Then for that same $\sigma$,
--
--   $$E(T)=E^{A'':B'}((\mathrm{id}_{A''}\otimes T)(\sigma_{A''A'})).$$
--
--   No convexity, separable-state normalization, or finite-supremum hypothesis is imposed. This identifies the channel measure with its implementing single-use resource.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 26, Theorem A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem A.1, PDF pp.25--26: SAME implementation witness, arbitrary
nonnegative LOCC monotone. The associated supremum is not assumed finite. -/
theorem imageImplementable_monotone (E : StateFunctional) (hE : IsDimensionChangingLOCCMonotone E)
    (T : Superop I J) (hT : IsChannel T) (sigma : Mat (A × I))
    (L : Superop ((I × A) × J) (Unit × J)) (himpl : ImplementsFrom T sigma L) :
    channelValue E T = (E A J (idTensorSuperop T sigma) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
