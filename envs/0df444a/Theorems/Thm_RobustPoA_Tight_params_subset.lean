-- Prove2me | Theorems.Thm_RobustPoA_Tight_params_subset
-- name    : RobustPoA.Tight.params_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:48.612581+00:00
-- url     : https://prove2.me/theorems/83535a41-bd37-49ae-8bf0-93df0eac020d
-- title:
--   §5.1, p. 24 — resourcewise smoothness implies game smoothness
-- statement:
--   Let $\mathcal C$ be a nonempty set of nonnegative, nondecreasing cost functions. Every parameter pair satisfying the resourcewise condition (35) makes every congestion game with costs from $\mathcal C$ smooth. In symbols,
--
--   $$\mathcal A(\mathcal C)\subseteq\mathcal A(\mathcal G(\mathcal C)).$$
--
--   This inclusion connects the local inequality for one resource to the smoothness parameters of the entire game class.
--
--   **Formalization Note** The class ranges over every finite number of players and resources and every nonempty strategy set, rather than a fixed game size.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), §5.1, p. 24, sentence before Proposition 5.2

import Definitions.Def_RobustPoA_Tight_Classes

namespace RobustPoA.Tight

/-- §5.1, p. 24, the sentence before Proposition 5.2: every parameter pair satisfying
the resourcewise constraints makes every game in the class smooth. -/
theorem params_subset (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) : smoothParams C ⊆ classParams C := by sorry

end RobustPoA.Tight
