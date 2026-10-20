-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_dampingBelowReceiverEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P08.dampingBelowReceiverEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:12:05.758591+00:00
-- url     : https://prove2.me/theorems/298812cb-9140-491c-878c-fed44e1affc8
-- title:
--   Damping potential below receiver entropy
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. Let $\theta^\gamma=(\mathrm{id}\otimes\mathcal A_\gamma)(\Phi_2)$. For every $0<\gamma<1$, $$V_F^{\to}(\theta^\gamma)<S(B)_{\theta^\gamma}=h_2((1-\gamma)/2).$$ The strict inequality compares the potential with receiver entropy and has no assertion of potential achievability.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 44, Damping potential below receiver entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.44, (10.5): potential strictly below receiver entropy for interior damping parameters. -/
theorem dampingBelowReceiverEntropy (g : ℝ) (hg : 0 < g) (hgUpper : g < 1) :
    statePotential (choi (finDamping g)) < vnEntropy (traceLeft (choi (finDamping g))) ∧
    vnEntropy (traceLeft (choi (finDamping g))) = binEntropy2 ((1 - g) / 2) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
