-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_subdiff_subset_eq_add_const
-- name    : RockafellarMaxMono.Cyclic.subdiff_subset_eq_add_const
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:14:34.376958+00:00
-- url     : https://prove2.me/theorems/ecae5a0a-8327-4561-8696-1a4f84d09169
-- title:
--   (3.6) — for lsc proper convex $f, g$ on a Banach space, $\partial g \supset \partial f$ implies $g = f + \mathrm{const}$
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$, and let $f$ and $g$ be lower semicontinuous proper convex functions on $E$ such that
--
--   $$
--   \partial g(x) \supset \partial f(x) \qquad \text{for all } x \in E . \tag{3.6}
--   $$
--
--   Then there is a real constant $c$ with
--
--   $$
--   g(x) = f(x) + c \qquad \text{for all } x \in E .
--   $$
--
--   Rockafellar notes that, given Theorem 1 of his 1966 paper and its Corollary 2, this statement is exactly what remains to prove Theorem B. It yields both the maximality of $\partial f$ among cyclically monotone operators and the uniqueness of $f$ up to an additive constant. The hypothesis is a one-sided inclusion.
--
--   **Formalization Note** "$\supset$" is non-strict inclusion. The constant $c$ is a real number (not $\pm\infty$); at points where $f(x) = +\infty$ the equation reads $g(x) = +\infty$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), pp. 214–216, §3, Proof of Theorem B, (3.6)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff

namespace RockafellarMaxMono.Cyclic

theorem subdiff_subset_eq_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f g : E → EReal)
    (hf : Shared.ProperConvex f) (hflsc : LowerSemicontinuous f)
    (hg : Shared.ProperConvex g) (hglsc : LowerSemicontinuous g)
    (hsub : ∀ x : E, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∃ c : ℝ, ∀ x : E, g x = f x + (c : EReal) := by sorry

end RockafellarMaxMono.Cyclic
