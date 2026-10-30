-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_ppt_strongConverse_capacity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.ppt_strongConverse_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:13:57.473443+00:00
-- url     : https://prove2.me/theorems/d63b6021-5b8c-4509-9663-5c83772ab595
-- title:
--   Strong-converse PPT-assisted quantum capacity bound
-- statement:
--   Let $\mathcal N_{A\to B}$ be a completely positive trace-preserving map on positive finite-dimensional registers. A real number $R$ is a strong-converse PPT-preserving-assisted quantum communication rate if, for every fixed $0\le\varepsilon<1$ and $\delta>0$, all sufficiently large positive integers $n$ admit no $(n,M,\varepsilon)$ protocol with $\log_2 M\ge n(R+\delta)$. Protocols use the channel $n$ times with arbitrary finite memories and PPT-preserving preparation, intermediate operations, and decoding; success means squared fidelity at least $1-\varepsilon$ with a maximally entangled state of integer rank $M\ge1$. Define $Q^{\mathrm{PPT\text{-}P},\leftrightarrow\dagger}(\mathcal N)$ as the infimum of these strong-converse rates. Then
--
--   $$Q^{\mathrm{PPT\text{-}P},\leftrightarrow\dagger}(\mathcal N)\le R_{\max}(\mathcal N).$$
--
--   This retains both PPT assistance and the strong-converse threshold, rather than replacing them with ordinary achievable-rate capacity.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 12, Corollary 5 / eq. (67)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- Corollary 5, PDF p.12, (67): upper bound on the strong-converse
PPT-P-assisted quantum capacity, defined as an infimum of strong-converse rates. -/
theorem ppt_strongConverse_capacity (N : Superop A B) (hN : IsChannel N) :
    strongConversePPTCapacity N ≤ channelMaxRains N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
