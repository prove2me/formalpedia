-- Prove2me | Theorems.Thm_PolyContract_bestResponse_existsUnique
-- name    : PolyContract.bestResponse_existsUnique
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:48:38.770485+00:00
-- url     : https://prove2.me/theorems/3d0efaca-3173-4342-bcf2-6a6e0fea4049
-- title:
--   §3, p.7 — the best response $x^\star(\alpha)$ exists and is unique
-- statement:
--   Let $(f,m,\beta)$ be an instance with a rank function $f$, rewards $m\ge0$ and quadratic costs $c(x)=\sum_e\beta_ex_e^2/2$ with $\beta_e>0$, on a finite nonempty ground set. For every share $\alpha\ge0$, the agent's objective
--   $$x\mapsto \alpha\,m^\top x-c(x)$$
--   has exactly one maximizer $x^\star(\alpha)$ over $P^{(+)}(f)$, and the reward under the best response with principal-favouring ties is $r(x^\star(\alpha))=m^\top x^\star(\alpha)$.
--
--   The objective is strictly concave and $P^{(+)}(f)$ is a nonempty compact polytope. The result makes the best response a function of the share, which every later statement uses.
--
--   Differences from the source:
--   - reading: the best response x⋆(α) is unique (existence assumed on p.6, "Both hold when c is continuous on the compact set P(+)(f)") → ∃! best response, i.e. existence and uniqueness; reason: the existence that p.6 asserts for continuous costs is part of the statement so that predicate-form milestones are not vacuous
--   - encoding: r(x⋆(α)) with ties broken in favour of the principal → brReward α (a supremum over all best responses) equals the reward of any best response; reason: pins the supremum form of the tie rule to the reward of the unique point
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), §3, p.7 (PDF p.8), with §2, p.6

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

/-- **§3, p.7: the best response exists and is unique** (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, §3, p.7, with §2, p.6): "at a
given share `α ≥ 0`, the agent chooses an effort allocation `x ∈ P(+)(f)` to maximize
`α m⊤x − c(x)`. This objective is strictly concave, so the best response `x⋆(α)` is unique."

For a valid instance with quadratic costs and every `α ≥ 0`, there is exactly one best response,
and the reward under the best response (with the principal-favouring tie rule) is its reward.

**Formalization Note** Existence is the paper's standing assumption (p.6: "Both hold when `c` is
continuous on the compact set `P(+)(f)`"); it is stated here so that the predicate form of the
other statements is not vacuous. The second clause pins `brReward`, an `sSup`, to the reward of
the unique best response. -/
theorem bestResponse_existsUnique {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (I : QuadInstance ι) (hI : I.Valid) (α : ℝ) (hα : 0 ≤ α) :
    (∃! x : ι → ℝ, I.IsBestResponse α x) ∧
      ∀ x : ι → ℝ, I.IsBestResponse α x → I.brReward α = I.reward x := by sorry

end PolyContract
