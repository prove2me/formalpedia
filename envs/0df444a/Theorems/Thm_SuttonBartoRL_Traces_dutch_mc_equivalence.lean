-- Prove2me | Theorems.Thm_SuttonBartoRL_Traces_dutch_mc_equivalence
-- name    : SuttonBartoRL.Traces.dutch_mc_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:58.510797+00:00
-- url     : https://prove2.me/theorems/09fb994b-d029-4b1a-890f-7f0ddd4015a3
-- title:
--   Eq. (12.14) (corrected): forward-view MC/LMS gives $w_T = a_{T-1} + \alpha G z_{T-1}$ with the dutch trace
-- statement:
--   Consider one episode of length $T \ge 1$ with feature vectors $x_0, \dots, x_{T-1} \in \mathbb R^d$, a step size $\alpha$, a single final return $G$ and an initial weight vector $w_0$. Let $F_t = I - \alpha x_t x_t^\top$.
--
--   1. The **forward view** runs the linear Monte Carlo (LMS) updates (12.13), $w_{t+1} = w_t + \alpha [G - w_t^\top x_t] x_t$ for $0 \le t < T$.
--   2. The **backward view** computes, without knowing $G$, the dutch trace $z_0 = x_0$, $z_t = z_{t-1} + (1 - \alpha z_{t-1}^\top x_t) x_t$, and the auxiliary vector $a_0 = F_0 w_0$, $a_t = a_{t-1} - \alpha x_t x_t^\top a_{t-1}$, for $1 \le t \le T - 1$.
--
--   Then the two views produce the same final weights:
--   $$
--   w_T = a_{T-1} + \alpha G\, z_{T-1}.
--   $$
--
--   This is the equivalence of forward and backward views in Monte Carlo learning. The same result as the MC/LMS algorithm is reached by an incremental algorithm with $O(d)$ time and memory per step. It shows that eligibility traces arise without temporal-difference learning.
--
--   **Formalization Note** The initialization of the auxiliary vector is **corrected** from the printed $a_0 = w_0$ to $a_0 = F_0 w_0$, as the book's own definition $a_t \doteq F_t\cdots F_0 w_0$ requires. With the printed initialization the claim is false: $d = 1$, $T = 1$, $x_0 = 1$, $\alpha = 1/2$, $w_0 = 1$, $G = 0$ gives $w_1 = 1/2$ but $a_0 + \alpha G z_0 = 1$. The identity holds for all real $\alpha$ and $G$ (the book's $\alpha$ is a positive step size). $T \ge 1$ is assumed so that $z_{T-1}$ and $a_{T-1}$ exist.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (12.14) and the recursions for z_t and a_t, p. 302, with Eq. (12.13), p. 301, and the concluding paragraph of §12.6, p. 303 (a_0 corrected to F_0 w_0)

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

namespace SuttonBartoRL.Traces

/-- Sutton & Barto, (12.14), p. 302 (corrected initialization `a_0 = F_0 w_0`): the final weight
vector `w_T` of the `T ≥ 1` forward-view linear MC/LMS updates (12.13) equals
`a_{T−1} + α G z_{T−1}`, where the dutch trace `z_t` and the auxiliary vector `a_t` are computed
by their incremental recursions, which do not use the return `G`. -/
theorem dutch_mc_equivalence {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    lmsWeights α G x w₀ T = auxVec α x w₀ (T - 1) + (α * G) • dutchTrace α x (T - 1) := by sorry

end SuttonBartoRL.Traces
