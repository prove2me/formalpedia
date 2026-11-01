-- Prove2me | Theorems.Thm_PWDB_theorem_1
-- name    : PWDB.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:40.781951+00:00
-- url     : https://prove2.me/theorems/2c25d66d-f5ee-4e88-9b3a-c21e41ef6323
-- title:
--   Theorem 1 — weak duality between (P) and (D)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$ ($i \in I$) satisfy assumption (F): each $f_i$, $i \in I_0 = \{0\} \cup I$, is proper, closed and convex.
--
--   Then
--   $$
--   \sup\,(\mathrm D) \le \inf\,(\mathrm P).
--   $$
--
--   In particular (D) is infeasible when (P) is unbounded, and (P) is infeasible when (D) is unbounded.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: index sets I, I0 = {0} ∪ I → Fintype ι (possibly empty), with the index 0 carried separately as f₀, w₀; reason: Lean convention; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Theorem 1, p.7; (F), (P), (D), p.7

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_ConvexProgram

namespace PWDB

/-- **Theorem 1 (Weak Duality)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Theorem 1, p.7):
"The infimum of (P) is larger or equal to the supremum of (D)."

Under assumption (F) (p.7: "The function `fi` is proper, closed and convex for each `i ∈ I0`"),
`sup (D) ≤ inf (P)`.

**Formalization Note** `E` is a finite-dimensional real inner product space (the paper's
`ℝ^{dx}`), `I` is a finite type, possibly empty. Values are in `EReal`: `pVal` is `+∞` when (P) is
infeasible and `dVal` is `−∞` when (D) is infeasible. (F) is the published
`TensorAHPE.IsProperClosedConvex` (never `−∞`, somewhere finite, lower semicontinuous, convex
epigraph), which for proper functions is the paper's "proper, closed and convex" (p.39). -/
theorem theorem_1 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f₀ : E → EReal) (f : ι → E → EReal)
    (hf₀ : TensorAHPE.IsProperClosedConvex f₀) (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i)) :
    dVal f₀ f ≤ pVal f₀ f := by sorry

end PWDB
