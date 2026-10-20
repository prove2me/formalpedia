-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_dampingStrictBeta
-- name    : QAlgorithms.Papers.Independent.Information100.P08.dampingStrictBeta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:10:14.798716+00:00
-- url     : https://prove2.me/theorems/384017d0-831e-4304-aee2-05b39474f3a0
-- title:
--   Strict damping comparison with C_beta
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. For every $0<\gamma<1$, $$U_F(\mathcal A_\gamma)<\log_2(1+\sqrt{1-\gamma}).$$ The right side is the evaluated $C_\beta$ benchmark cited in the source. This states the strict comparison, without identifying every finite-order geometric divergence with that benchmark.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 34, Strict damping comparison with C_beta

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.34, (8.20): strict comparison with the evaluated C_beta curve on the interior. -/
theorem dampingStrictBeta (g : ℝ) (hg : 0 < g) (hgUpper : g < 1) :
    channelPotential (finDamping g) < Real.logb 2 (1 + Real.sqrt (1 - g)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
