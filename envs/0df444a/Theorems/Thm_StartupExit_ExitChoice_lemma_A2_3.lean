-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_A2_3
-- name    : StartupExit.ExitChoice.lemma_A2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:56.507488+00:00
-- url     : https://prove2.me/theorems/232831da-d789-45f3-9b1e-d3bb2b3e6f39
-- title:
--   Lemma A2.3, Online Appendix A2 — for c = 0, ∂Π^F/∂θ < ∂Π^L/∂θ off the kink, and Π^F > Π^L for all θ ∈ [0, 1]
-- statement:
--   Assume the standing assumptions and $c=0$, and let $\kappa=\frac{w-1}{w+X(2,n)+\pi_B(n)}$. Then
--
--   1. for every $\theta\in(0,1)$ with $\theta\neq\kappa$, $\Pi^L$ has derivative $w+X(2,n)$ at $\theta$, and $\Pi^F$ is differentiable at $\theta$ with
--   $$\frac{\partial\Pi^F}{\partial\theta}<\frac{\partial\Pi^L}{\partial\theta}=w+X(2,n);$$
--   2. if $m=2$, $\Pi^F$ is not differentiable at $\theta=\kappa$;
--   3. for every $\theta\in[0,1]$, $\Pi^F(\theta)>\Pi^L(\theta)$.
--
--   When flexibility is free, the startup never commits to the late market.
--
--   **Formalization Note** The page adds that $\Pi^F$ is not differentiable at $\theta=\kappa$. For $m\ge3$ that clause is false, since $g(-1,m)=0$ makes the right derivative from (A2.2) equal to $0$, the left derivative; only $m=2$ has a true kink (there $g(-1,2)=1$ and the right derivative is $-\kappa\,\pi_B(n)\,(w+X(2,n)+\pi_B(n))<0$). It is therefore stated for $m=2$ only (part 2). The derivative claim is stated on the open interval $(0,1)$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 33–34), Lemma A2.3

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem lemma_A2_3 (P : Params) (hS : P.Standing) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) 1, θ ≠ kink P →
      HasDerivAt (PiL P) (P.w + X2 P.n) θ ∧
      ∃ d : ℝ, HasDerivAt (PiF P 0) d θ ∧ d < P.w + X2 P.n) ∧
    (P.m = 2 → ¬ DifferentiableAt ℝ (PiF P 0) (kink P)) ∧
    (∀ θ ∈ Set.Icc (0 : ℝ) 1, PiL P θ < PiF P 0 θ) := by sorry

end StartupExit.ExitChoice
