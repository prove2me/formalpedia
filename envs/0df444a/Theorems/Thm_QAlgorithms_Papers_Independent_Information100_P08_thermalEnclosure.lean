-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_thermalEnclosure
-- name    : QAlgorithms.Papers.Independent.Information100.P08.thermalEnclosure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:14:24.580371+00:00
-- url     : https://prove2.me/theorems/9ea431d0-0a45-47f7-b876-f22c05709450
-- title:
--   Certified thermal potential enclosure
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. Let $\rho^\star=\theta^{1/2,1/10}$. Then $$0.45252350<V_F^{\to}(\rho^\star)<0.45252360.$$ The endpoints are exact rational decimals. This encloses the optimized potential; the lower endpoint is not a claimed operational randomness rate.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 48, Certified thermal potential enclosure

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.48,70, (10.33): exact rational enclosure on the potential, not on an achievable rate. -/
theorem thermalEnclosure :
    0.45252350 < statePotential thermalState ∧ statePotential thermalState < 0.45252360 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
