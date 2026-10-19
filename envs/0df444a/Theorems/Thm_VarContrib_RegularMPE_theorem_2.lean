-- Prove2me | Theorems.Thm_VarContrib_RegularMPE_theorem_2
-- name    : VarContrib.RegularMPE.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:37.830113+00:00
-- url     : https://prove2.me/theorems/0a7bec82-4689-4a8f-8039-0fd8243d50ac
-- title:
--   Theorem 2, pp. 15–16 — in the symmetric game, regular contribution at rate u of (6) is an MPE with payoff V of (4)
-- statement:
--   Consider the symmetric game ($\pi_1=\pi_2=\pi$, $k_1=k_2=k$) under the standing assumptions and Assumptions 1–3. Let $V$ be the solution (4) of the single decision maker problem, that is, $\theta\in I$ and $A$ are such that
--   $$V(x)=\begin{cases}k(x-\theta)+V(\theta) & x<\theta,\\ (R\pi)(x)+A\varphi(x) & x\ge\theta\end{cases}$$
--   is twice continuously differentiable on $I$, and define
--   $$u(x)=\begin{cases}-\tfrac1k\big(\mathcal AV(x)+\pi(x)\big) & x<\theta,\\ 0 & x\ge\theta.\end{cases}\tag{6}$$
--   Suppose $u\in\mathcal U$. Then
--
--   1. the symmetric profile in which both players contribute at the regular rate $d\xi_{it}=u(Z_t)dt$ is a Markov perfect equilibrium: from every initial state $x\in I$, no player gains by deviating to any admissible control, while the other keeps contributing at rate $u$;
--   2. each player's payoff is $V$: for every $x\in I$ and every solution $Z$ of $dZ_t=[\mu(Z_t)+2u(Z_t)]dt+\sigma(Z_t)dW_t$, $Z_0=x$,
--   $$V_i(x;\xi)=\mathbb E\int_0^\infty e^{-rt}\big(\pi(Z_t)-k\,u(Z_t)\big)dt=V(x).$$
--
--   The free-rider effect does not move the threshold $\theta$ of the single decision maker; it replaces the instantaneous reflection at $\theta$ by gradual contribution below $\theta$.
--
--   **Formalization Note.** The pair $(\theta,A)$ is not chosen: smoothness of $V$ at $\theta$ is the condition (A.1) of Lemma 1's proof, which determines it. Nonnegativity of $u$ is not assumed; it is part of the conclusion. Deviations range over all adapted controls with finite expected discounted cost and integrable running profit (the others pay $-\infty$). Statements hold for every solution of the state equations; existence of solutions is not posed.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, pp. 15–16, Theorem 2, (4), (6)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting
import Definitions.Def_VarContrib_RegularMPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- Theorem 2 (Kwon, pp. 15–16): in the symmetric game, let `V` be the solution (4) of the
single decision maker problem (`θ ∈ I` and `A` such that `V ∈ C²(I)`) and `u` the rate (6).
If `u ∈ 𝒰`, then both players contributing at the regular rate `dξ_{it} = u(Z_t) dt` is a
Markov perfect equilibrium, and each player's payoff from every `x ∈ I` is `V(x)`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (hst : Standing m S) (θ A : ℝ) (hθ : θ ∈ m.I)
    (hV : ContDiffOn ℝ 2 (Vsol m S θ A) m.I) (hu : InU m (uEq m S θ A)) :
    IsRegularMPE m S (fun _ => uEq m S θ A) ∧
    ∀ x ∈ m.I, ∀ Z : ℝ≥0 → Ω → ℝ,
      IsStateSol m S (fun y => m.μ y + uEq m S θ A y + uEq m S θ A y) x (fun _ _ => 0) Z →
        regPay m S (uEq m S θ A) Z = Vsol m S θ A x := by sorry

end VarContrib.RegularMPE
