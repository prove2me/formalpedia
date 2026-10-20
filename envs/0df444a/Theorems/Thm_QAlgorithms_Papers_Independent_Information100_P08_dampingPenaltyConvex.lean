-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_dampingPenaltyConvex
-- name    : QAlgorithms.Papers.Independent.Information100.P08.dampingPenaltyConvex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:04:34.663382+00:00
-- url     : https://prove2.me/theorems/fcbac19f-4ada-49d5-adc1-1a8692ee030d
-- title:
--   Lemma 8.1: damping penalty
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. Fix $\gamma\in[0,1]$ and let $\rho(t,z)=\begin{pmatrix}1-t&z\\\bar z&t\end{pmatrix}$, where $0\le t\le1$ and $|z|^2\le t(1-t)$. Define $g_\gamma(t)=h_2((1-\gamma)t)-H((1-\gamma)t(1-t))$. Then $$S(\mathcal A_\gamma(\rho(t,z)))-f_{\mathcal A_\gamma}(\rho(t,z))\ge g_\gamma(t),\qquad g_\gamma\text{ is convex on }[0,1].$$ Both parameter endpoints are included. The environment measurement used in the source is a mathematical argument, not a receiver resource.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 31, Lemma 8.1: damping penalty

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.30-32, Lemma 8.1: coherence-removal inequality and diagonal-penalty convexity. -/
theorem dampingPenaltyConvex (g : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, Complex.normSq z ≤ t * (1 - t) →
      dampingPenalty g t ≤ vnEntropy (finDamping g (qubitInput t z)) -
        channelFormation (finDamping g) (qubitInput t z)) ∧
    ConvexOn ℝ (Set.Icc 0 1) (dampingPenalty g) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
