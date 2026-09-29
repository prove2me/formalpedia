-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_7_max_attained
-- name    : ValuativeSYZ.lemma_3_7_max_attained
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T12:02:28.722886+00:00
-- url     : https://prove2.me/theorems/51d54626-ae8c-4b98-8a26-9a5a975b8281
-- title:
--   Lemma 3.7: the suprema defining the $c$-transform are attained
-- statement:
--   **Lemma 3.7.** For $\varphi \in P_c$ the two suprema defining the $c$-transform are attained:
--   $$\varphi(x) \;=\; \max_{p \in B}\big(c(x,p) - \varphi^{c}(p)\big), \qquad
--   \varphi^{c}(p) \;=\; \max_{x \in X}\big(c(x,p) - \varphi(x)\big).$$
--   In the paper the two spaces are the essential skeleton $\mathrm{Sk}(X)$ and the space $B_y$ of
--   limiting tropical theta functions, both compact, and the cost function is continuous, being
--   Lipschitz in $x$ and continuous in $p$ by construction of $B_y$ in the $C^0$-topology. Attainment is
--   what makes the conjugate sets of §4.3 — the non-archimedean analogue of the gradient image in the
--   Alexandrov formulation of the real Monge–Ampère equation — well behaved.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15-16, Lemma 3.7

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.7.** For a continuous cost function on compact spaces, the suprema defining the
`c`-transform of a function of the class `P_c` and of its transform are both attained. -/
theorem lemma_3_7_max_attained {X B : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace B] [CompactSpace B] [Nonempty B]
    (c : X → B → ℝ) (hc : Continuous fun z : X × B => c z.1 z.2)
    (φ : X → ℝ) (hφ : φ ∈ Pc c) :
    (∀ x : X, ∃ p : B, φ x = c x p - ctransform c φ p) ∧
      (∀ p : B, ∃ x : X, ctransform c φ p = c x p - φ x) := by sorry

/-! ### Milestones: subadditivity on the semigroup and the cost function (§3.5) -/

end ValuativeSYZ
