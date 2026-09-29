-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_finite_subdiff_subset_eq_add_const
-- name    : RockafellarMaxMono.Cyclic.finite_subdiff_subset_eq_add_const
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:11:47.141353+00:00
-- url     : https://prove2.me/theorems/eb980363-817a-4106-856c-3819117432c0
-- title:
--   §3, pp. 214–215 — finite continuous case: $\partial g \supset \partial f$ implies $g = f + \mathrm{const}$
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$, and let $f, g : V \to \mathbb{R}$ be convex functions which are everywhere finite and continuous. Suppose that
--
--   $$
--   \partial g(x) \supset \partial f(x) \qquad \text{for all } x \in V .
--   $$
--
--   Then there is a real constant $c$ with
--
--   $$
--   g(x) = f(x) + c \qquad \text{for all } x \in V .
--   $$
--
--   This is the first case of Rockafellar's proof of Theorem B: for finite continuous convex functions, a one-sided inclusion of subdifferentials already forces the functions to differ by a constant. The general case is reduced to this one by passing to the conjugates $(f+j)^*$ and $(g+j)^*$ on the dual space.
--
--   **Formalization Note** "$\supset$" is non-strict inclusion. Subdifferentials are those of the real-valued functions regarded as functions into $(-\infty, +\infty]$. $V$ is an arbitrary real Banach space because the proof applies this case on $E^*$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), pp. 214–215, §3, Proof of Theorem B, the case where f and g are everywhere finite and continuous

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff

namespace RockafellarMaxMono.Cyclic

theorem finite_subdiff_subset_eq_add_const {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (kconv : ConvexOn ℝ Set.univ k) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) :
    ∃ c : ℝ, ∀ x : V, k x = h x + c := by sorry

end RockafellarMaxMono.Cyclic
