-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_exactThermalEnvelope
-- name    : QAlgorithms.Papers.Independent.Information100.P08.exactThermalEnvelope
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:07:45.417081+00:00
-- url     : https://prove2.me/theorems/7a2bc0c0-f9f6-441e-9849-35161c334721
-- title:
--   Proposition 10.2: exact fixed-input envelope
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. For a bipartite state $\rho_{AB}$, let $V_F^{\to}(\rho)$ be the supremum of $I(X;B)+\sum_xp_xE_F(A^{\prime};B)_{\omega^x}$ over all finite Alice instruments with classical outcome $X$ and arbitrary finite retained quantum system $A^{\prime}$. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal A_\gamma$ be qubit amplitude damping, with Kraus operators $\operatorname{diag}(1,\sqrt{1-\gamma})$ and $\sqrt\gamma\lvert0\rangle\langle1\rvert$. Define $\mathcal G_{\gamma,\nu}(\tau)=(1-\nu)\mathcal A_\gamma(\tau)+\nu X\mathcal A_\gamma(X\tau X)X$, where $X$ is the bit flip. Its normalized Choi state is $\theta^{\gamma,\nu}=(\mathrm{id}\otimes\mathcal G_{\gamma,\nu})(\Phi_2)$, with $\Phi_2$ the projector of $(\lvert00\rangle+\lvert11\rangle)/\sqrt2$. For $\gamma,\nu\in[0,1]$, set $a=1-\gamma$, $b(t)=\gamma\nu+at$, $\Delta(t)=\gamma[\nu(1-\nu)+a(t-\nu)^2]$, and $c=\max\{\sqrt a-\gamma\sqrt{\nu(1-\nu)},0\}$. Define $g_{\gamma,\nu}(t,u)=H(\Delta(t)+au)-H(c^2u)$ on $0\le t\le1$, $0\le u\le t(1-t)$. Let $\ell_{\gamma,\nu}(t)=\min_{0\le u\le t(1-t)}g_{\gamma,\nu}(t,u)$, and let $\operatorname{co}\ell$ be its greatest convex minorant on $[0,1]$. Then $$V_F^{\to}(\theta^{\gamma,\nu})=h_2(b(1/2))-(\operatorname{co}\ell_{\gamma,\nu})(1/2).$$ Moreover an input ensemble with at most four possibly mixed members, average $I_2/2$, attains the corresponding channel objective at this value. No convexity of $\ell$ itself is assumed.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 47, Proposition 10.2: exact fixed-input envelope

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.46-47, Proposition 10.2: exact convex envelope and attainment by four possibly
mixed inputs. Convexity of populationPenalty itself is not assumed. -/
theorem exactThermalEnvelope (g n : ℝ) (hg : g ∈ Set.Icc (0 : ℝ) 1)
    (hn : n ∈ Set.Icc (0 : ℝ) 1) :
    statePotential (choi (thermalChannel g n)) =
      binEntropy2 (thermalPopulation g n (1 / 2)) - convexEnvelope g n (1 / 2) ∧
    ∃ e : Ensemble (Fin 2), e.size ≤ 4 ∧ ensembleAverage e = maximallyMixed 2 ∧
      channelObjective (thermalChannel g n) e = statePotential (choi (thermalChannel g n)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
