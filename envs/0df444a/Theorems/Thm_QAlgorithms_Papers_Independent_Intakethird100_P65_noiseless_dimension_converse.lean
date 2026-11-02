-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P65_noiseless_dimension_converse
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P65.noiseless_dimension_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:00:41.408719+00:00
-- url     : https://prove2.me/theorems/d64c2b68-73e4-49b1-b206-fb6b43da165d
-- title:
--   §VI: exact noiseless-dimension converse
-- statement:
--   All systems have finite positive dimension and fixed computational bases. Matrix order is Loewner order and logarithms are base two.
--
--   Let $\mathcal N:A\to B$ be CPTP and let $m_1,m_2\ge1$ be integers. Suppose $\mathcal N$ exactly simulates $\mathrm{id}_{m_1}$ with NS assistance, and $\mathrm{id}_{m_2}$ exactly simulates $\mathcal N$ with NS assistance. Then
--
--   $$m_1\le m_2.$$
--
--   Exact simulation means minimum half-diamond error zero. No nonzero-error version is asserted; this is the noiseless-dimension converse in the discussion.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, PDF p. 15, §VI: exact noiseless-dimension converse

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

noncomputable section

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)

open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)

open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

/-- Section VI, exact noiseless-dimension converse, PDF p.15.
Both simulations use NS assistance and exact error zero. -/
theorem noiseless_dimension_converse (N : Superop A B) (hN : IsChannel N)
    (m1 m2 : ℕ) (h1 : 0 < m1) (h2 : 0 < m2)
    (hforward : minimumError .ns N (fun X : Mat (Fin m1) => X) = 0)
    (hbackward : minimumError .ns (fun X : Mat (Fin m2) => X) N = 0) :
    m1 ≤ m2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P65

end
