-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_globalThermalCertificate
-- name    : QAlgorithms.Papers.Independent.Information100.P08.globalThermalCertificate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:13:35.683994+00:00
-- url     : https://prove2.me/theorems/cf5edf9e-075c-4eac-9ab7-3c83d66ec6f1
-- title:
--   Global affine thermal penalty certificate
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. For $\gamma,\nu\in[0,1]$, set $a=1-\gamma$, $b(t)=\gamma\nu+at$, $\Delta(t)=\gamma[\nu(1-\nu)+a(t-\nu)^2]$, and $c=\max\{\sqrt a-\gamma\sqrt{\nu(1-\nu)},0\}$. Define $g_{\gamma,\nu}(t,u)=H(\Delta(t)+au)-H(c^2u)$ on $0\le t\le1$, $0\le u\le t(1-t)$. Let $\rho^\star=\theta^{1/2,1/10}$ and exact rational constants $\alpha=0.4287673$, $\beta=0.7391729$. On the full physical domain, $$g_{1/2,1/10}(t,u)\ge\alpha+\beta(t-1/2),\qquad 0\le t\le1,\quad0\le u\le t(1-t).$$ Consequently $$V_F^{\to}(\rho^\star)\le h_2(3/10)-\alpha<0.45252360.$$ This is an unconditional mathematical inequality to be proved; it assumes neither an optimizer's correctness nor a checker-success predicate.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 48, Global affine thermal penalty certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.48,69-70, (10.30)-(10.31): unconditional global affine certificate and its
potential consequence. All finite decimals are exact rationals; no checker-success hypothesis. -/
theorem globalThermalCertificate :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) (t * (1 - t)),
      certificateAlpha + certificateBeta * (t - 1 / 2) ≤ thermalPenalty (1 / 2) (1 / 10) t u) ∧
    statePotential thermalState ≤ binEntropy2 (3 / 10) - certificateAlpha ∧
    binEntropy2 (3 / 10) - certificateAlpha < 0.45252360 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
