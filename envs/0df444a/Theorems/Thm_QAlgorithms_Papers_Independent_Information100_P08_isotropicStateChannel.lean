-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_isotropicStateChannel
-- name    : QAlgorithms.Papers.Independent.Information100.P08.isotropicStateChannel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:08:22.944986+00:00
-- url     : https://prove2.me/theorems/d5af4cf8-26fc-4def-a246-4fe12eb32890
-- title:
--   Proposition 11.2: state–channel identity
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. For $p\in[0,1]$, let $\mathcal D_p(\tau)=(1-p)\tau+pI_2/2$ and $\rho^{(p)}=(\mathrm{id}\otimes\mathcal D_p)(\Phi_2)$, where $\Phi_2$ is the normalized maximally entangled qubit projector. Then $$V_F^{\to}(\rho^{(p)})=U_F(\mathcal D_p).$$ The equality is specific to this covariant family; it is not asserted for every channel.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 52, Proposition 11.2: state–channel identity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.52-53, Proposition 11.2: the isotropic Pauli orbit meets the fixed Choi average. -/
theorem isotropicStateChannel (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    statePotential (isotropic p) = channelPotential (depolarizing 2 p) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
