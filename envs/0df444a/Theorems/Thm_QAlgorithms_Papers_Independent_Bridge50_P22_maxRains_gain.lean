-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_maxRains_gain
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.maxRains_gain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:11:25.044047+00:00
-- url     : https://prove2.me/theorems/04b7a181-7b18-4f88-8cf0-6f3bd4cdd13f
-- title:
--   One-use max-Rains entanglement gain bound
-- statement:
--   Let $\mathcal N_{A\to B}$ be a completely positive trace-preserving channel and let $\rho_{A'AB'}$ be any density operator. All four registers have positive finite dimension, and fixed orthonormal product bases specify partial transpose. Set $\omega_{A'BB'}=(\operatorname{id}_{A'}\otimes\mathcal N\otimes\operatorname{id}_{B'})(\rho_{A'AB'})$. The max-Rains relative entropy $R_{\max}(X;Y)$ minimizes the base-two max-relative entropy over the positive operators $\sigma_{XY}$ with $\|T_Y(\sigma)\|_1\le1$; $R_{\max}(\mathcal N)$ maximizes this entanglement over pure channel inputs with a reference isomorphic to $A$. Then
--
--   $$R_{\max}(A';BB')_\omega\le R_{\max}(\mathcal N)+R_{\max}(A'A;B')_\rho.$$
--
--   This bounds the increase in max-Rains entanglement for an arbitrary mixed input, including inputs with preshared entanglement.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 7, Proposition 1 / eqs. (28)–(29)

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

/-- Proposition 1, PDF pp.7–9, (28)–(29): full one-use max-Rains gain bound.
No PPT, separability or purity condition is imposed on the mixed input. -/
theorem maxRains_gain (N : Superop A B) (hN : IsChannel N)
    (rho : Mat ((L × A) × R)) (hrho : IsDensityMatrix rho) :
    stateMaxRains (channelUse N rho) ≤ channelMaxRains N + stateMaxRains rho := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
