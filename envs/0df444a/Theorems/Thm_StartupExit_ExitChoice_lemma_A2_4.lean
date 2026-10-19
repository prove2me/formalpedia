-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_lemma_A2_4
-- name    : StartupExit.ExitChoice.lemma_A2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:42.477266+00:00
-- url     : https://prove2.me/theorems/2db3a2ae-e7b5-4139-8d17-85894122375d
-- title:
--   Lemma A2.4, Online Appendix A2 — for c = 0, Π^F > Π^E iff θ > θ_FE, with θ_FE strictly between the kink and θ̃
-- statement:
--   Assume the standing assumptions and $c=0$. There is $\theta_{FE}$ with
--
--   $$\frac{w-1}{w+X(2,n)+\pi_B(n)}<\theta_{FE}<\tilde\theta$$
--
--   such that, for every $\theta\in[0,1]$, the profit from flexibility strictly exceeds the profit from early commitment exactly when $\theta>\theta_{FE}$:
--
--   $$\Pi^F(\theta)>\Pi^E\iff\theta>\theta_{FE}.$$
--
--   $\theta_{FE}$ is the threshold between early commitment and flexibility when the early market is free; scaling it by $1/\phi(R-c)$ gives the threshold $\theta_L$ of Proposition 1.
--
--   **Formalization Note** The $n\to\infty$ part of the proof is not formalized.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 34), Lemma A2.4

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem lemma_A2_4 (P : Params) (hS : P.Standing) :
    ∃ θFE : ℝ, kink P < θFE ∧ θFE < thetaTilde P ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, PiE P < PiF P 0 θ ↔ θFE < θ := by sorry

end StartupExit.ExitChoice
