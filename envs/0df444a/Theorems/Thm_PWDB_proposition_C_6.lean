-- Prove2me | Theorems.Thm_PWDB_proposition_C_6
-- name    : PWDB.proposition_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:51.408209+00:00
-- url     : https://prove2.me/theorems/b3c9b5c2-f1b0-484a-aa2c-834b7ee5384e
-- title:
--   Proposition C.6 — a bounded primal feasible region gives a strict dual Slater point
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$ ($i \in I$) satisfy assumption (F): each $f_i$, $i \in I_0 = \{0\} \cup I$, is proper, closed and convex.
--
--   If the feasible region of (P) is nonempty and bounded, then (D) admits a strict Slater point: a point $(w_0, \{w_i\}, \lambda)$ with $w_0 + \sum_i w_i = 0$, $\lambda > 0$, lying in the relative interior of the domain of the objective of (D).
--
--   This supplies the dual Slater points used in Section 3 to dualize embedded problems.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - encoding: vector equations Σ wi = 0 and constraints λ ≥ 0 (ν ≥ 0) in a Slater point (Definition 1) → the scalar linear equations ⟨v, Σ wi⟩ = 0 for all v, and the affine inequalities −λi ≤ 0 (−νiℓ ≤ 0); reason: the same feasible set; all these functions are finite and affine, so conditions (i)–(iii) of Definition 1 are those of the coordinate representation, and strictness gives λ > 0 as in the proof of Proposition C.6 (p.47)
--   - encoding: index sets I, I0 = {0} ∪ I → Fintype ι (possibly empty), with the index 0 carried separately as f₀, w₀; reason: Lean convention; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Proposition C.6, p.68 (proof pp.46–47)

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_ConvexProgram
import Definitions.Def_PWDB_Slater

namespace PWDB

/-- **Proposition C.6 (Sufficient Condition for a Dual Slater Point)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, Proposition C.6, p.68): "If the feasible region of (P) is nonempty and bounded,
then (D) admits a strict Slater point."

**Formalization Note** Under (F) (`TensorAHPE.IsProperClosedConvex`). The feasible region of (P)
is `pFeas` (p.40: constraints hold and `f0(x) ≠ +∞`). A strict Slater point of (D) is
`StrictSlaterMax` (Definition 2 and p.7) on `E × (I → E) × (I → ℝ)` with inequality constraints
`−λi ≤ 0` and equations `Σ_{i∈I0} wi = 0`: so `Σ wi = 0`, `λ > 0` and the point lies in
`ri(dom(−objective of (D)))`. -/
theorem proposition_C_6 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f₀ : E → EReal) (f : ι → E → EReal)
    (hf₀ : TensorAHPE.IsProperClosedConvex f₀) (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i))
    (hne : (pFeas f₀ f).Nonempty) (hbdd : Bornology.IsBounded (pFeas f₀ f)) :
    ∃ pS, StrictSlaterMax (dObj f₀ f) (dIneq ι) (dEq ι) pS := by sorry

end PWDB
