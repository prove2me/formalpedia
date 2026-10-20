-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_fixedAverageChoi
-- name    : QAlgorithms.Papers.Independent.Information100.P08.fixedAverageChoi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:06:55.634609+00:00
-- url     : https://prove2.me/theorems/4ea40f02-bb00-4b16-ae2b-6e3b5a15f821
-- title:
--   Proposition 9.3: fixed-average Choi correspondence
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. Let $\pi=I_A/d_A$, $\lvert\Phi\rangle=d_A^{-1/2}\sum_j\lvert j,j\rangle$, and $\theta_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(\lvert\Phi\rangle\langle\Phi\rvert)$. With $g_{\mathcal N}(\tau)=S(\mathcal N(\tau))-f_{\mathcal N}(\tau)$, $$V_F^{\to}(\theta_{\mathcal N})=S(\mathcal N(\pi))-\inf_{\sum_xp_x\tau_x=\pi}\sum_xp_xg_{\mathcal N}(\tau_x)\le U_F(\mathcal N).$$ All finite ensembles in the infimum may have mixed members. The fixed average is essential to the source problem.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 42, Proposition 9.3: fixed-average Choi correspondence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.42-43, Proposition 9.3: the average input is fixed to I/d_A, including mixed members. -/
theorem fixedAverageChoi {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    statePotential (choi N) = vnEntropy (N (maximallyMixed a)) - constrainedPenalty N (maximallyMixed a) ∧
    statePotential (choi N) ≤ channelPotential N := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
