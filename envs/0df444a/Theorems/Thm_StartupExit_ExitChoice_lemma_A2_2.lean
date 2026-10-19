-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_A2_2
-- name    : StartupExit.ExitChoice.lemma_A2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:46.737086+00:00
-- url     : https://prove2.me/theorems/f5f0e760-a760-47fa-9a02-7fc3b9a95cd2
-- title:
--   Lemma A2.2, Online Appendix A2 — for c = 0, Π^F is continuous, equals w + X(2, m) up to the kink, then first declines and then increases
-- statement:
--   Assume the standing assumptions and $c=0$, and let $\kappa=\frac{w-1}{w+X(2,n)+\pi_B(n)}$. The profit from flexibility $\theta\mapsto\Pi^F(\theta)$ satisfies:
--
--   1. it is continuous on $[0,1]$;
--   2. for $\theta\in[0,\kappa]$ it does not depend on $\theta$: $\Pi^F(\theta)=w+X(2,m)=\Pi^E$;
--   3. there is $\theta_0\in(\kappa,1)$ such that $\Pi^F$ is strictly decreasing on $[\kappa,\theta_0]$ and strictly increasing on $[\theta_0,1]$.
--
--   $$\Pi^F(\theta)=\Pi^E\ (\theta\le\kappa),\qquad \Pi^F\searrow\ \text{on }[\kappa,\theta_0],\qquad \Pi^F\nearrow\ \text{on }[\theta_0,1].$$
--
--   The dip below $\Pi^E$ just above the kink is why low-capability startups prefer to commit to the early market even when flexibility is free.
--
--   **Formalization Note** "First declines and then increases" is rendered as strict antitonicity on $[\kappa,\theta_0]$ and strict monotonicity on $[\theta_0,1]$ for some $\theta_0$ strictly inside $(\kappa,1)$. The $n\to\infty$ sentence of part (ii) is not formalized.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 32–33), Lemma A2.2

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem lemma_A2_2 (P : Params) (hS : P.Standing) :
    ContinuousOn (PiF P 0) (Set.Icc 0 1) ∧
    (∀ θ ∈ Set.Icc (0 : ℝ) (kink P), PiF P 0 θ = PiE P) ∧
    ∃ θ0 : ℝ, kink P < θ0 ∧ θ0 < 1 ∧
      StrictAntiOn (PiF P 0) (Set.Icc (kink P) θ0) ∧
      StrictMonoOn (PiF P 0) (Set.Icc θ0 1) := by sorry

end StartupExit.ExitChoice
