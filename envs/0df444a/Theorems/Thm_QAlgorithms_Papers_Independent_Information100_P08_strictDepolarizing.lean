-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P08_strictDepolarizing
-- name    : QAlgorithms.Papers.Independent.Information100.P08.strictDepolarizing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:03:54.454122+00:00
-- url     : https://prove2.me/theorems/fca0e080-f673-45d7-b1bc-86d31f947154
-- title:
--   Proposition 7.2: strictness of the bound
-- statement:
--   All systems below have finite positive dimension. States are positive semidefinite matrices of trace one, channels are completely positive trace-preserving maps, and entropies are in bits. Write $S$ for von Neumann entropy and $E_F(A;B)$ for the pure convex roof of marginal entropy across the indicated cut. For a channel $\mathcal N:A\to B$ and input state $\tau$, let $f_{\mathcal N}(\tau)$ be the entanglement of formation of its reference–output state obtained from a purification of $\tau$. For a finite ensemble $e=(p_x,\tau_x)_x$, write $\bar\tau=\sum_xp_x\tau_x$ and $F_{\mathcal N}(e)=S(\mathcal N(\bar\tau))-\sum_xp_xS(\mathcal N(\tau_x))+\sum_xp_x f_{\mathcal N}(\tau_x)$. Define $U_F(\mathcal N)=\sup_e F_{\mathcal N}(e)$, allowing mixed ensemble members. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with the continuous $0\log0=0$ convention, and $H(v)=h_2((1-\sqrt{1-4v})/2)$ for $0\le v\le1/4$. For the qubit depolarizing channel $\mathcal D_p(\tau)=(1-p)\tau+pI_2/2$ and every $0<p<2/3$, $$U_F(\mathcal D_p)>1-h_2(p/2).$$ This is a strict gap above the known unassisted capacity value, not an achievable feedback advantage.
-- source:
--   Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, PDF p. 28, Proposition 7.2: strictness of the bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF pp.28-29, Proposition 7.2: strict bound gap, without a feedback-advantage claim. -/
theorem strictDepolarizing (p : ℝ) (hp : 0 < p) (hpUpper : p < 2 / 3) :
    1 - binEntropy2 (p / 2) < channelPotential (depolarizing 2 p) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P08
