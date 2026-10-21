-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_proposition_1_cost_thresholds
-- name    : StartupExit.ExitChoice.proposition_1_cost_thresholds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:43.255024+00:00
-- url     : https://prove2.me/theorems/2fde1ba0-f6d4-498f-aa31-239cd7901e22
-- title:
--   Proof of Proposition 1, Online Appendix A2 — c̄ by φ(R − c̄) = θ_FE/θ̃ and c̲ by Π^F = Π^L at θ = 1 are unique in [0, R], and 0 < c̲ < c̄ < R
-- statement:
--   Assume the standing assumptions and let $\theta_{FE}$ be the threshold of Lemma A2.4: $\kappa<\theta_{FE}<\tilde\theta$ and, at $c=0$, $\Pi^F(\theta)>\Pi^E$ iff $\theta>\theta_{FE}$ for $\theta\in[0,1]$. Then there are costs $\underline c,\bar c$ with
--
--   $$0<\underline c<\bar c<R$$
--
--   such that
--
--   1. $\phi(R-\bar c)=\theta_{FE}/\tilde\theta$, and $\bar c$ is the only $c\in[0,R]$ with $\phi(R-c)=\theta_{FE}/\tilde\theta$;
--   2. $\Pi^F(\underline c,1)=\Pi^L(1)$, and $\underline c$ is the only $c\in[0,R]$ at which the type $\theta=1$ is indifferent between flexibility and late commitment.
--
--   These are the two cost thresholds of Proposition 1: above $\bar c$ the startup never chooses flexibility, and below $\underline c$ it never commits to the late market.
--
--   **Formalization Note** $\theta_{FE}$ is passed with its Lemma A2.4 property as a hypothesis. The page defines $\bar c$ and $\underline c$ as "the unique value" and "implicitly"; existence and uniqueness over $[0,R]$ are both stated.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 36), proof of Proposition 1, definitions of c̄ and c̲ and "φ(R − c̄) < φ(R − c̲) ⇔ c̲ < c̄"

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem proposition_1_cost_thresholds (P : Params) (hS : P.Standing) (θFE : ℝ)
    (hFE : kink P < θFE ∧ θFE < thetaTilde P ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, PiE P < PiF P 0 θ ↔ θFE < θ) :
    ∃ cl cu : ℝ, 0 < cl ∧ cl < cu ∧ cu < P.R ∧
      P.φ (P.R - cu) = θFE / thetaTilde P ∧
      (∀ c ∈ Set.Icc 0 P.R, P.φ (P.R - c) = θFE / thetaTilde P → c = cu) ∧
      PiF P cl 1 = PiL P 1 ∧
      (∀ c ∈ Set.Icc 0 P.R, PiF P c 1 = PiL P 1 → c = cl) := by sorry

end StartupExit.ExitChoice
