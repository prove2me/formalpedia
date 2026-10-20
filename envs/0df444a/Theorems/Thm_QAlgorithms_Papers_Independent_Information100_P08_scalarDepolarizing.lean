-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_scalarDepolarizing
-- name    : QAlgorithms.Papers.Independent.Information100.P08.scalarDepolarizing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:03:23.910529+00:00
-- url     : https://prove2.me/theorems/e8bed391-3544-486c-8392-86fbc282a470
-- title:
--   Proposition 7.1: scalar depolarizing formula
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. Let $\mathcal D_p(\tau)=(1-p)\tau+pI_2/2$, $p\in[0,1]$, and $\kappa=\max\{1-3p/2,0\}$. Set $E(c)=h_2((1+\sqrt{1-c^2})/2)$. The scalar maximum is attained and $$U_F(\mathcal D_p)=\max_{0\le r\le1}\left\{1-h_2\!\left(\frac{1+(1-p)r}{2}\right)+E(\kappa\sqrt{1-r^2})\right\}.$$ The parameter $r$ is the input Bloch-vector length, allowing mixed inputs.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 27, Proposition 7.1: scalar depolarizing formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.27, Proposition 7.1: scalar maximum with actual attainment, including p=0,1. -/
theorem scalarDepolarizing (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1,
      channelPotential (depolarizing 2 p) = depolarizingObjective p r ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, depolarizingObjective p s ≤ depolarizingObjective p r := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
