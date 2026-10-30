-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_eMax_amortization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.eMax_amortization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:17:33.183738+00:00
-- url     : https://prove2.me/theorems/527a34f0-86f8-4dc9-9047-b2e0cc484f69
-- title:
--   Max-relative entanglement is unchanged by amortization
-- statement:
--   Let $\mathcal N_{A\to B}$ be a completely positive trace-preserving map between positive finite-dimensional complex Hilbert spaces. For a bipartite density operator $\tau$, define $E_{\max}(\tau)$ as its minimum base-two max-relative entropy to a separable density operator. Define $E_{\max}(\mathcal N)$ by maximizing output entanglement over pure inputs on $SA$ with $S\simeq A$. Let $E_{\max,A}(\mathcal N)$ be the supremum of $E_{\max}(A';BB')_\omega-E_{\max}(A'A;B')_\rho$ over all normalized mixed states $\rho_{A'AB'}$ and all positive finite ancillary dimensions, with $\omega=(\operatorname{id}_{A'}\otimes\mathcal N\otimes\operatorname{id}_{B'})(\rho)$. Then
--
--   $$E_{\max,A}(\mathcal N)=E_{\max}(\mathcal N).$$
--
--   This is the result of [CMH17] for which the present paper supplies an alternative convex-optimization argument. The separable comparison set distinguishes it from max-Rains amortization collapse.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 12, Section 5 / eq. (68)

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

/-- PDF pp.12,16, (68), attributed to [CMH17]: Emax amortization collapse.
The supremum ranges over every normalized mixed input and every positive
finite pair of memories, including trivial memories. -/
theorem eMax_amortization (N : Superop A B) (hN : IsChannel N) :
    amortizedEMax N = channelEMax N := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
