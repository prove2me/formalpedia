-- Prove2me | Theorems.Thm_PersPricingDist_PersonalA_proposition_4
-- name    : PersPricingDist.PersonalA.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:09.337015+00:00
-- url     : https://prove2.me/theorems/947cc424-d570-4c09-a6bc-fc08d46e6fcd
-- title:
--   Proposition 4, p. 15 — contribution thresholds under personalized pricing by A
-- statement:
--   Suppose A charges personalized prices. There exist two functions of A's contribution, $\beta_{PP}$ and $\beta_{PU}$, chosen jointly and applicable to every market with $0<s<v<1$ and $X\ge v/s$, such that
--   $$\begin{aligned}
--   \text{dual distribution in PP}&\iff\beta>\beta_{PP}(\alpha),\\
--   \text{dual distribution in PU}&\iff\beta>\beta_{PU}(\alpha),\\
--   \beta_{PP}(\alpha)&<\beta_{PU}(\alpha).
--   \end{aligned}$$
--
--   Here PP means that both firms personalize prices, while PU means that B charges one uniform price before A chooses personalized responses. Thus B must make a larger contribution to justify dual distribution in PU than in PP.
--
--   **Formalization Note** Dual distribution requires a strict improvement over personalized mono distribution for some nonnegative wholesale price. The cutoff ordering is stated for every real argument; values outside the admissible range of $\alpha$ can be extended freely.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84a…c253), p. 15, Proposition 4 (PDF 17); proof OA pp. 4–13 (PDF 37–46)

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

namespace PersPricingDist.PersonalA

theorem proposition_4 :
    ∃ betaPP betaPU : ℝ → ℝ,
      (∀ M : Model, M.Standing → (M.DualPP ↔ betaPP M.alpha < M.beta)) ∧
      (∀ M : Model, M.Standing → (M.DualPU ↔ betaPU M.alpha < M.beta)) ∧
      (∀ a : ℝ, betaPP a < betaPU a) := by sorry

end PersPricingDist.PersonalA
