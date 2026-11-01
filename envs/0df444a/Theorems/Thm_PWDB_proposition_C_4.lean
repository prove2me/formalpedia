-- Prove2me | Theorems.Thm_PWDB_proposition_C_4
-- name    : PWDB.proposition_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:00.286157+00:00
-- url     : https://prove2.me/theorems/bff483a8-54e3-4482-a2c9-9c661043d168
-- title:
--   Proposition C.4 — conjugates of sums
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $g_j : E \to \overline{\mathbb R}$, $j \in J$ (finite), be proper convex functions. Then for every $w \in E$
--   $$
--   \Big(\sum_{j\in J} g_j\Big)^*(w) \le \inf_{\{w_j\}_{j\in J}} \Big\{ \sum_{j\in J} g_j^*(w_j) \;\Big|\; \sum_{j\in J} w_j = w \Big\}. \tag{28}
--   $$
--   If $\bigcap_{j\in J} \operatorname{ri}(\operatorname{dom} g_j) \ne \emptyset$, the inequality is an equality for every $w$, and (for $J \ne \emptyset$) the infimum is attained.
--
--   The bound gives the weak-duality step of Theorem 1; the equality case identifies the Lagrangian dual of (D) with (P).
--
--   **Formalization Note** "Proper convex" is the published `RockafellarMaxMono.Shared.ProperConvex`; closedness is not assumed.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: proper convex gj : ℝ^{dx} → R̄ → RockafellarMaxMono.Shared.ProperConvex (never −∞, somewhere finite, the convexity inequality in EReal); reason: for functions that never take −∞ this is convexity of the epigraph; same instances
--   - reading: the minimum is attained for every w (functions g1, …, gJ) → attainment asserted when J is nonempty; reason: the list g1, …, gJ has J ≥ 1; for an empty family and w ≠ 0 the constraint Σ wj = w has no solution, so nothing can be attained
--   - encoding: the finite list g1, …, gJ → Fintype J, possibly empty, in (28) and in the equality; reason: Lean convention; the empty sum is 0 and both statements hold there
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition C.4, eq. (28), p.65

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_PWDB_conj

namespace PWDB

/-- **Proposition C.4 (Conjugates of Sums)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2,
Proposition C.4, p.65): "If `g1, …, gJ : ℝ^{dx} → R̄` are proper convex functions, then
`(Σ_{j∈J} gj)∗(w) ≤ inf_{{wj}j∈J} {Σ_{j∈J} gj∗(wj) | Σ_{j∈J} wj = w} ∀w ∈ ℝ^{dx}`. (28)
If `∩_{j∈J} ri(dom(gj)) ≠ ∅`, then the inequality is tight, and the minimum is attained for every
`w`."

**Formalization Note** "Proper convex" is the published `RockafellarMaxMono.Shared.ProperConvex`
(never `−∞`, somewhere finite, the convexity inequality in `EReal`); closedness is not assumed, as
in the paper. Sums are `EReal` sums; since each `gj > −∞`, no sum meets `⊤ + ⊥`. The infimum is
taken in `EReal`. Attainment is stated for a nonempty index set: the list `g1, …, gJ` has `J ≥ 1`,
and for an empty family the constraint `Σ wj = w` has no solution when `w ≠ 0`. `ri` is
`intrinsicInterior ℝ`, `dom` is `AubinLipschitz.effDom`. -/
theorem proposition_C_4 {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype J]
    (g : J → E → EReal) (hg : ∀ j, RockafellarMaxMono.Shared.ProperConvex (g j)) :
    (∀ w : E, conj (fun x => ∑ j, g j x) w ≤
      ⨅ (v : J → E) (_ : ∑ j, v j = w), ∑ j, conj (g j) (v j)) ∧
    ((⋂ j, intrinsicInterior ℝ (AubinLipschitz.effDom (g j))).Nonempty →
      ∀ w : E, conj (fun x => ∑ j, g j x) w =
          ⨅ (v : J → E) (_ : ∑ j, v j = w), ∑ j, conj (g j) (v j) ∧
        (Nonempty J → ∃ v : J → E, ∑ j, v j = w ∧
          conj (fun x => ∑ j, g j x) w = ∑ j, conj (g j) (v j))) := by sorry

end PWDB
