-- Prove2me | Theorems.Thm_SuspensionContract_AlwaysWork_ec67_value_matching
-- name    : SuspensionContract.AlwaysWork.ec67_value_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:21.672513+00:00
-- url     : https://prove2.me/theorems/14ac34b7-5575-4376-aee9-0abf521d4330
-- title:
--   (EC.67), p. ec32 — C¹(θ̲), m(θ̲) solve the value-matching and smooth-pasting equations (36)–(37)
-- statement:
--   Under the standing assumptions of the model, let $\underline\theta\in(0,\bar w]$ and put $c=C^1(\underline\theta)$, $m=m(\underline\theta)$ as in (EC.67). Then the suspension-state solution $V_c(w)=\underline v+w+c\,w^{r/\rho}$ meets the line $\bar V+m(w-\bar w)$ at $\underline\theta$ with the same slope:
--   $$V_{C^1(\underline\theta)}(\underline\theta)=\bar V+m(\underline\theta)(\underline\theta-\bar w),\qquad V_{C^1(\underline\theta)}'(\underline\theta)=m(\underline\theta).$$
--
--   These are the value-matching (36) and smooth-pasting (37) equations of Lemma 5 with $\underline\theta$ in place of $\underline\theta_K$; they reduce Lemma 5 to the single equation (38), i.e. $\psi_1(\underline\theta)=K$.
--
--   **Formalization Note.** The paper says "for any $\underline\theta\in[0,\bar w]$"; at $\underline\theta=0$ the derivative $V_c'(0)$ is not finite, so the identity is stated for $\underline\theta\in(0,\bar w]$. Equation (36) is written with $\underline\theta$ at the place where Lemma 5 prints a free $w$ (a misprint; see Lemma 5). The derivative is the ordinary derivative, which exists at $\underline\theta>0$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec32, EC.3.7 (proof of Lemma 5), (EC.67)

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting
import Definitions.Def_SuspensionContract_AlwaysWork_ValueFunctions

namespace SuspensionContract.AlwaysWork

/-- (EC.67), p. ec32: for every `θ̲ ∈ (0, w̄]`, `c = C¹(θ̲)` and `m = m(θ̲)` satisfy the
value-matching equation (36) and the smooth-pasting equation (37) at `θ̲`. -/
theorem ec67_value_matching (P : Params) (hP : P.Standing) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ : θ ≤ P.wbar) :
    P.Vc (P.C1 θ) θ = P.Vbar + P.mOf θ * (θ - P.wbar) ∧
      deriv (P.Vc (P.C1 θ)) θ = P.mOf θ := by sorry

end SuspensionContract.AlwaysWork
