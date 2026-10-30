-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_maxRains_amortization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.maxRains_amortization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:10:25.487992+00:00
-- url     : https://prove2.me/theorems/5032ad57-c640-4383-88ff-5df7201be33d
-- title:
--   Max-Rains information is unchanged by amortization
-- statement:
--   Let $\mathcal N_{A\to B}$ be a completely positive trace-preserving channel between positive finite-dimensional complex Hilbert spaces. For a bipartite density operator $\tau_{XY}$, write $R_{\max}(X;Y)_\tau$ for the minimum of $D_{\max}(\tau\Vert\sigma)$ over positive operators $\sigma$ satisfying $\|T_Y(\sigma)\|_1\le1$, where $T_Y$ is partial transpose in the fixed product basis and $D_{\max}(\tau\Vert\sigma)=\inf\{\lambda:\tau\le2^\lambda\sigma\}$. Define $R_{\max}(\mathcal N)$ by maximizing the output max-Rains entanglement over pure states on $SA$ with $S\simeq A$. Define $R_{\max,A}(\mathcal N)$ as the supremum of $R_{\max}(A';BB')_\omega-R_{\max}(A'A;B')_\rho$ over every normalized mixed state $\rho_{A'AB'}$ and all positive finite dimensions of $A',B'$, with $\omega=(\operatorname{id}_{A'}\otimes\mathcal N\otimes\operatorname{id}_{B'})(\rho)$. Then
--
--   $$R_{\max,A}(\mathcal N)=R_{\max}(\mathcal N).$$
--
--   Thus preshared entanglement cannot increase the net max-Rains entanglement generated in one channel use. All information quantities are measured in bits.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 9, Corollary 2 / eq. (42)

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

/-- Corollary 2, PDF p.9, (42), announced on pp.1,4: max-Rains amortization
collapse for every finite-dimensional CPTP channel. All ancillary dimensions
and mixed input states are optimized in amortizedMaxRains. -/
theorem maxRains_amortization (N : Superop A B) (hN : IsChannel N) :
    amortizedMaxRains N = channelMaxRains N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
