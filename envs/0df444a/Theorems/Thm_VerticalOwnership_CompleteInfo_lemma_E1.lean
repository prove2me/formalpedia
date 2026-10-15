-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_lemma_E1
-- name    : VerticalOwnership.CompleteInfo.lemma_E1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:42.941438+00:00
-- url     : https://prove2.me/theorems/abd4494b-ffbf-44b1-ab08-8be1c7b6e785
-- title:
--   Lemma E1, p. 44 — a unique β̲ ∈ [0,1) exists such that G(β) ≥ 0 if and only if β ≥ β̲
-- statement:
--   Let $\mu_i \in \{\mu_L, \mu_H\}$ and, for $\beta \in [0,1]$, let $G(\beta)$ be the retailer's accounting payoff gain from placing the optimal advance order $q^* = \mu_i + F^{-1}(z_r(\beta))$ instead of relying on the capacity $\mu_i + F^{-1}(z_s)$ the supplier builds for free. Then there is a unique $\underline\beta \in [0,1)$ such that for all $\beta \in [0,1]$
--   $$G(\beta) \ge 0 \iff \beta \ge \underline\beta.$$
--
--   The lemma says that financing the entire capacity becomes worthwhile exactly from a threshold ownership share on, and that the threshold is below full ownership.
--
--   **Formalization Note** The lemma is stated for $G$ as defined from the payoffs (with $q^*$ the explicit maximizer), not for its closed form. The paper's proof asserts without argument that $G < 0$ whenever $z_r(\beta) \le z_s$; that step is part of what must be proved here.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 44, Lemma E1

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem lemma_E1 (M : Model) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ)) :
    ∃! βlow : ℝ, βlow ∈ Set.Ico (0 : ℝ) 1 ∧
      ∀ β ∈ Set.Icc (0 : ℝ) 1, (0 ≤ M.G β μ (μ + M.Finv (M.zrβ β)) ↔ βlow ≤ β) := by sorry

end VerticalOwnership.CompleteInfo
