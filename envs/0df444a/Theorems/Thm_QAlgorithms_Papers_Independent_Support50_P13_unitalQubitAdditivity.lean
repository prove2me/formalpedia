-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P13_unitalQubitAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P13.unitalQubitAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:21:30.063588+00:00
-- url     : https://prove2.me/theorems/08e7b634-a3f3-4606-8670-6ef4506bf24c
-- title:
--   Unital qubit channels: norm multiplicativity and entropy and Holevo additivity
-- statement:
--   Let $\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ be a completely positive trace-preserving linear map satisfying $\Phi(I_2)=I_2$. Let $K\ge1$ be an integer and let $\Omega:M_K(\mathbb C)\to M_K(\mathbb C)$ be any completely positive trace-preserving linear map. A density matrix is positive semidefinite with trace one. For a positive matrix $A$ and a finite real $p\ge1$, put $\|A\|_p=(\operatorname{Tr}A^p)^{1/p}$ and $\nu_p(\Lambda)=\sup_\rho\|\Lambda(\rho)\|_p$, where $\rho$ ranges over every input density matrix. Write $S(\rho)=-\operatorname{Tr}\rho\log\rho$, with natural logarithms and $0\log0=0$, and $S_{\min}(\Lambda)=\inf_\rho S(\Lambda(\rho))$. The Holevo quantity $\chi^*(\Lambda)$ is the supremum of $S(\sum_i\pi_i\Lambda(\rho_i))-\sum_i\pi_i S(\Lambda(\rho_i))$ over all finite ensembles of density matrices with nonnegative weights summing to one. Then
--
--   $$
--   \begin{aligned}
--   \nu_p(\Omega\otimes\Phi)&=\nu_p(\Omega)\nu_p(\Phi) &&\text{for every real }p\ge1,\\
--   S_{\min}(\Omega\otimes\Phi)&=S_{\min}(\Omega)+S_{\min}(\Phi),\\
--   \chi^*(\Omega\otimes\Phi)&=\chi^*(\Omega)+\chi^*(\Phi).
--   \end{aligned}
--   $$
--
--   The product-channel optimizations include all entangled input density matrices. These equalities assert that entanglement between the two channel inputs does not improve these three optimized quantities.
-- source:
--   Additivity for a class of unital qubit channels, arXiv:quant-ph/0103156v2, PDF p. 4, Theorem 1, equations (5)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P13

open QAlgorithms.Papers.Independent.Gap48.P03
  (productChannel maximumOutputPNorm holevoQuantity depolarizingNormFactor
    phaseChannel qubitPauli)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0103156v2, PDF p.4, Theorem 1, (5)-(7).
Phi is an arbitrary unital qubit channel, with no standard-form restriction.
Omega is an arbitrary finite positive-dimensional CPTP endomap.
The imported minimumOutputEntropy takes values in the extended nonnegative reals;
on these finite-dimensional channels its values are finite and measured in nats. -/
theorem unitalQubitAdditivity
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hPhiUnital : Phi 1 = 1)
    (K : ℕ) (hK : 0 < K)
    (Omega : Superop (Fin K) (Fin K)) (hOmega : IsChannel Omega) :
    (∀ p : ℝ, 1 ≤ p →
      maximumOutputPNorm (productChannel Omega Phi) p =
        maximumOutputPNorm Omega p * maximumOutputPNorm Phi p) ∧
    minimumOutputEntropy (productChannel Omega Phi) =
      minimumOutputEntropy Omega + minimumOutputEntropy Phi ∧
    holevoQuantity (productChannel Omega Phi) =
      holevoQuantity Omega + holevoQuantity Phi := by sorry

end QAlgorithms.Papers.Independent.Support50.P13

end
