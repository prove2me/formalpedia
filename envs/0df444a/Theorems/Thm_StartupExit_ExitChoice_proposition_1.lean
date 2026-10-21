-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_proposition_1
-- name    : StartupExit.ExitChoice.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:52.661406+00:00
-- url     : https://prove2.me/theorems/dfbb43f0-c2b7-49e7-8d9c-df12b9139d8b
-- title:
--   Proposition 1, p. 15 — costs c̲ < c̄: cheap early market ⇒ flexible iff θ > θ_L; intermediate ⇒ early, flexible or late; costly ⇒ early iff θ ≤ θ̃
-- statement:
--   Assume the standing assumptions: common value $w>1$, $2\le m<n$ early and late buyers, resources $R>0$, and $\phi$ strictly increasing and continuous on $[0,R]$ with $\phi(0)=0$, $\phi(R)=1$. A startup of capability $\theta\in[0,1]$ facing cost $c\in[0,R]$ of trying the early market chooses among early commitment ($\Pi^E$), late commitment ($\Pi^L$) and flexibility ($\Pi^F$), maximizing profit and breaking ties towards early, then late, then flexible. Write $\phi=\phi(R-c)$ and $\tilde\theta$ for the type with $\Pi^E=\Pi^L$.
--
--   There exist $\underline c,\bar c$ with $0<\underline c<\bar c<R$ such that:
--
--   1. **(cheap early market)** if $0\le c<\underline c$, there is $\theta_L$ with
--   $$\frac{w-1}{\phi\,(w+X(1,n))}<\theta_L<\tilde\theta$$
--   such that every type tries the early market (never commits late) and it chooses flexibility if and only if $\theta>\theta_L$;
--   2. **(intermediate cost)** if $\underline c<c<\bar c$, there are $\theta_L<\theta_H$ with $\tilde\theta<\theta_H<1$ such that types $\theta\ge\theta_H$ commit to the late market, types $\theta<\theta_H$ try the early market, types $\theta_L<\theta<\theta_H$ choose flexibility, and types $\theta\le\theta_L$ commit to the early market;
--   3. **(costly early market)** if $\bar c\le c\le R$, types $\theta\le\tilde\theta$ commit to the early market and types $\theta>\tilde\theta$ commit to the late market.
--
--   The proposition shows that the timing of exit is non-monotone in capability: low-capability startups commit early, high-capability startups commit late (unless the early market is cheap), and intermediate ones stay flexible.
--
--   **Formalization Note** "Tries the early market" means the choice is early or flexible, i.e. not late. Part (i) is posed for $c<\underline c$, not $c\le\underline c$ as printed: at $c=\underline c$ the type $\theta=1$ is indifferent between flexibility and late commitment, and under the tie rule it commits late. Part (ii) also states that $\theta\le\theta_L$ commits early, which the proof establishes ("commitment to early exit is optimal for $\theta\le\theta_L$", PDF 36) and which pins the reading of "always tries the early market". The main-text version is used (the appendix restatement has $\theta_L\in(0,\tilde\theta)$ and "$\theta\le\theta_H$" in (ii), which conflicts with (ii)'s first sentence at $\theta_H$ under the tie rule). The choice is defined from the three profits only, so the thresholds are not built into the model.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), p. 15 (PDF 16), Proposition 1; proof in Online Appendix A2 (PDF 36)

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem proposition_1 (P : Params) (hS : P.Standing) :
    ∃ cl cu : ℝ, 0 < cl ∧ cl < cu ∧ cu < P.R ∧
      (∀ c ∈ Set.Ico 0 cl, ∃ θL : ℝ,
          (P.w - 1) / (P.φ (P.R - c) * (P.w + X1 P.n)) < θL ∧ θL < thetaTilde P ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            choice P c θ ≠ Strategy.late ∧ (choice P c θ = Strategy.flexible ↔ θL < θ)) ∧
      (∀ c ∈ Set.Ioo cl cu, ∃ θL θH : ℝ,
          thetaTilde P < θH ∧ θH < 1 ∧ θL < θH ∧
          ∀ θ ∈ Set.Icc (0 : ℝ) 1,
            (θH ≤ θ → choice P c θ = Strategy.late) ∧
            (θ < θH → choice P c θ ≠ Strategy.late) ∧
            (θL < θ → θ < θH → choice P c θ = Strategy.flexible) ∧
            (θ ≤ θL → choice P c θ = Strategy.early)) ∧
      (∀ c ∈ Set.Icc cu P.R, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
          (θ ≤ thetaTilde P → choice P c θ = Strategy.early) ∧
          (thetaTilde P < θ → choice P c θ = Strategy.late)) := by sorry

end StartupExit.ExitChoice
