-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_dampingMaximumOutput
-- name    : QAlgorithms.Papers.Independent.Information100.P08.dampingMaximumOutput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:10:56.586992+00:00
-- url     : https://prove2.me/theorems/e27693f7-4ffe-43e8-a597-725f4793148e
-- title:
--   Maximum output entropy of damping
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. For $\gamma\in[0,1]$, the maximum output entropy is $$\sup_{\tau\in\mathcal S(\mathbb C^2)}S(\mathcal A_\gamma(\tau))=\begin{cases}1,&\gamma\le1/2,\\ h_2(1-\gamma),&\gamma>1/2.\end{cases}$$ Both branches agree at $\gamma=1/2$. This evaluates the entropy benchmark, not the operational capacity.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 34, Maximum output entropy of damping

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.34: maximum output entropy of amplitude damping, with the shared boundary included. -/
theorem dampingMaximumOutput (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    sSup {r | ∃ rho : Matrix (Fin 2) (Fin 2) ℂ,
      IsDensityMatrix rho ∧ r = vnEntropy (finDamping g rho)} =
      if g ≤ 1 / 2 then 1 else binEntropy2 (1 - g) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
