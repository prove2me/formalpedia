-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_eMax_gain
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.eMax_gain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:16:48.793084+00:00
-- url     : https://prove2.me/theorems/79f6436c-0857-4ebb-b582-10cf81a888eb
-- title:
--   One-use max-relative-entanglement gain bound
-- statement:
--   Let $\mathcal N_{A\to B}$ be a finite-dimensional quantum channel and let $\rho_{A'AB'}$ be an arbitrary normalized mixed state on positive finite-dimensional registers. Set $\omega_{A'BB'}=(\operatorname{id}_{A'}\otimes\mathcal N\otimes\operatorname{id}_{B'})(\rho)$. For a bipartite state, $E_{\max}$ is the minimum base-two max-relative entropy to a separable density operator; $E_{\max}(\mathcal N)$ maximizes output $E_{\max}$ over pure inputs with a reference isomorphic to $A$. Then
--
--   $$E_{\max}(A';BB')_\omega\le E_{\max}(\mathcal N)+E_{\max}(A'A;B')_\rho.$$
--
--   This result is attributed to Christandl and Müller-Hermes [CMH17] and is reproved in the present paper. It bounds net entanglement gain even in the presence of arbitrary finite preshared entanglement.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 14, Proposition 8 ([CMH17]) / eqs. (79)–(80)

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

/-- Proposition 8 ([CMH17]), PDF pp.14–16, (79)–(80): full one-use Emax
gain inequality, reproved here by convex optimization. Output is computed from rho. -/
theorem eMax_gain (N : Superop A B) (hN : IsChannel N)
    (rho : Mat ((L × A) × R)) (hrho : IsDensityMatrix rho) :
    eMax (channelUse N rho) ≤ channelEMax N + eMax rho := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
