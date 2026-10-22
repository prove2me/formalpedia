-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_Vsol_monotoneOn
-- name    : VarContrib.RegularMPE.Vsol_monotoneOn
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T23:59:38.150837+00:00
-- url     : https://prove2.me/theorems/9c475ea9-3731-4d8c-80ed-ed058727ee78
-- title:
--   Proof of Theorem 2, condition (i), p. 38 — the solution V of (4) is non-decreasing on I
-- statement:
--   Consider the symmetric game ($\pi_1=\pi_2=\pi$, $k_1=k_2=k$) on the state interval $I=(a,b)$ under the standing assumptions and Assumptions 1–3. Let $V$ be the solution (4) of the single decision maker problem: $\theta\in I$ and $A\in\mathbb R$ are such that
--
--   $$
--   V(x)=\begin{cases}k(x-\theta)+V(\theta) & x<\theta,\\ (R\pi)(x)+A\varphi(x) & x\ge\theta,\end{cases}
--   $$
--
--   is twice continuously differentiable on $I$, where $(R\pi)(x)=\mathbb E^x\int_0^\infty e^{-rt}\pi(X_t)\,dt$ is the resolvent of the flow profit along the uncontrolled diffusion and $\varphi$ is the decreasing fundamental solution of $\mathcal A\varphi=0$. Then $V$ is non-decreasing on $I$:
--
--   $$
--   x,y\in I,\ x\le y\ \Longrightarrow\ V(x)\le V(y).
--   $$
--
--   This is the monotonicity used in the proof of Theorem 2 to verify condition (i) of the verification Theorem 1 ("$V(\cdot)\in C^2(I)$ and $V(\cdot)$ is non-decreasing"); together with the bound $V\le \pi_M/r+|A|\varphi(\theta)$ it makes $V$ an admissible candidate payoff function $U$ in Theorem 1.
--
--   **Formalization Note.** The hypotheses are exactly those of the formalized Theorem 2 (`Standing`, $\theta\in I$, $V\in C^2(I)$); the pair $(\theta,A)$ is determined by the $C^2$ requirement as in the proof of Lemma 1.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, p. 38 (Appendix A, Proof of Theorem 2, verification of condition (i): 'V(·) ∈ C²(I) and V(·) is non-decreasing'), with V of (4), p. 10

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- Proof of Theorem 2, condition (i) (Kwon, p. 38): the solution `V` of (4) of the single
decision maker problem (`θ ∈ I` and `A` such that `V ∈ C²(I)`) is non-decreasing on `I`. -/
theorem Vsol_monotoneOn {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (θ A : ℝ) (hθ : θ ∈ m.I)
    (hV : ContDiffOn ℝ 2 (Vsol m S θ A) m.I) :
    MonotoneOn (Vsol m S θ A) m.I := by sorry

end VarContrib.RegularMPE
