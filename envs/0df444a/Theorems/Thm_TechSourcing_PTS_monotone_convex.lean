-- Prove2me | Theorems.Thm_TechSourcing_PTS_monotone_convex
-- name    : TechSourcing.PTS.monotone_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:38.121831+00:00
-- url     : https://prove2.me/theorems/6786b5bd-43a2-47be-bc94-1117671bf835
-- title:
--   Proof of Proposition 1, p. Appendix-13 — γ̂ decreasing in a; F increasing in a, and a quadratic, convex function of β
-- statement:
--   Under the standing assumptions, with the other parameters held fixed:
--
--   1. $a\mapsto\hat\gamma=\big(3(a+b)-\sqrt{9a^2+10ab+b^2}\big)/(4b)$ is strictly decreasing on $(0,\infty)$;
--   2. $a\mapsto F$ is strictly increasing on $(0,\infty)$, where $F$ is the comparison function of the proof of Proposition 1;
--   3. $\beta\mapsto F$ is a quadratic function with positive leading coefficient: there are reals $q_2>0$, $q_1$, $q_0$ with
--   $$F\big|_{\beta}=q_2\beta^2+q_1\beta+q_0\quad\text{for every real }\beta .$$
--
--   These are the monotonicity and convexity facts from which the thresholds $\bar a_T(\beta)$ and $\bar\beta_L(a)\le\bar\beta_H(a)$ of Proposition 1 arise.
--
--   **Formalization Note** "Increasing" and "decreasing" are formalized strictly, which is what the threshold argument needs; "quadratic, convex" is formalized as an exact quadratic with positive leading coefficient, valid for every real $\beta$.
-- source:
--   Zhang & Lee, Investment Strategies for Sourcing a New Technology in the Presence of a Mature Technology, SSRN 3269249 (version of 23 Mar 2021), p. Appendix-13 (PDF 39), proof of Proposition 1 ("We note that γ̂ is decreasing in a and, hence, …")

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

namespace TechSourcing.PTS

/-- Proof of Proposition 1 (p. Appendix-13): with the other parameters fixed, `γ̂` is strictly
decreasing in `a`, the comparison function `F` is strictly increasing in `a`, and `F` is a quadratic,
convex function of `β`. -/
theorem monotone_convex (P : Params) (hP : P.Standing) :
    StrictAntiOn (fun a : ℝ => gammaHat { P with a := a }) (Set.Ioi 0) ∧
      StrictMonoOn (fun a : ℝ => Fcmp { P with a := a }) (Set.Ioi 0) ∧
      ∃ q₂ q₁ q₀ : ℝ, 0 < q₂ ∧
        ∀ β : ℝ, Fcmp { P with β := β } = q₂ * β ^ 2 + q₁ * β + q₀ := by sorry
end TechSourcing.PTS
