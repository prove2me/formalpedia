-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_equation_A2_2
-- name    : StartupExit.ExitChoice.equation_A2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:59.682026+00:00
-- url     : https://prove2.me/theorems/6b3b7a94-52f9-43f3-b3c5-2b14e7390266
-- title:
--   Eq. (A2.2), Online Appendix A2 — for c = 0 and θ above the kink, ∂Π^F/∂θ = G(v̲*)(w+X(2,n)) − θg(v̲*)π_B(n)(w+X(2,n)+π_B(n))
-- statement:
--   Assume the standing assumptions and $c=0$ (so $\phi(R)=1$). For every $\theta$ strictly between the kink $\frac{w-1}{w+X(2,n)+\pi_B(n)}$ and $1$, the flexible profit $\Pi^F$ is differentiable in $\theta$ with
--
--   $$\frac{\partial\Pi^F}{\partial\theta}=G(\underline v^*(\theta),m)\,\bigl(w+X(2,n)\bigr)-\theta\,g(\underline v^*(\theta),m)\,\pi_B(n)\,\bigl(w+X(2,n)+\pi_B(n)\bigr). \tag{A2.2}$$
--
--   This derivative formula drives Lemmas A2.2 and A2.3: its sign is that of the slack in (A2.1), and it is below the slope $w+X(2,n)$ of $\Pi^L$.
--
--   **Formalization Note** Stated as `HasDerivAt` of $\theta\mapsto\Pi^F(0,\theta)$ at each $\theta$ in the open interval; the endpoint $\theta=1$ is excluded because $\theta$ ranges over $[0,1]$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 33), proof of Lemma A2.3, eq. (A2.2); also in the proof of Lemma A2.2

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem equation_A2_2 (P : Params) (hS : P.Standing) :
    ∀ θ ∈ Set.Ioo (kink P) 1,
      HasDerivAt (PiF P 0)
        (Gcdf (vStar P θ) P.m * (P.w + X2 P.n) -
          θ * gdens (vStar P θ) P.m * piB P.n * (P.w + X2 P.n + piB P.n)) θ := by sorry

end StartupExit.ExitChoice
