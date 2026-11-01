-- Prove2me | Theorems.Thm_PWDB_theorem_2
-- name    : PWDB.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:04.5389+00:00
-- url     : https://prove2.me/theorems/352a1389-683d-44fe-a8c1-0d361eef3d6a
-- title:
--   Theorem 2 — strong duality between (P) and (D)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$ ($i \in I$) satisfy assumption (F): each $f_i$, $i \in I_0 = \{0\} \cup I$, is proper, closed and convex.
--
--   1. If (P) admits a Slater point, then $\inf(\mathrm P) = \sup(\mathrm D)$ and (D) is solvable.
--   2. If (D) admits a Slater point, then $\inf(\mathrm P) = \sup(\mathrm D)$ and (P) is solvable.
--   3. If the feasible region of (P) is nonempty and bounded, then $\inf(\mathrm P) = \sup(\mathrm D)$ and (P) is solvable.
--   4. If the feasible region of (D) is nonempty and bounded, then $\inf(\mathrm P) = \sup(\mathrm D)$ and (D) is solvable.
--
--   Slater points are those of Definitions 1–2 (for (D): a maximization problem in $(w_0, \{w_i\}, \lambda)$ with the linear constraints $\sum w_i = 0$, $\lambda \ge 0$). Solvability follows p.40: an infeasible problem counts as solvable.
--
--   Differences from the source:
--   - generalization: ℝ^{dx}, ℝ^{dz} → finite-dimensional real inner product spaces E, F; reason: every ℝ^d with the dot product is such a space, so the Lean statement specializes to the printed one
--   - encoding: (F): fi proper, closed and convex, values in R̄ → TensorAHPE.IsProperClosedConvex (never −∞, somewhere finite, lower semicontinuous, convex epigraph), values in EReal; reason: for a proper function the paper's 'closed' (p.39) is lower semicontinuity; same instances
--   - encoding: optimal values, feasible regions and solvability of p.40 → EReal ⨅/⨆ over the feasible region; feasibility excludes the bad objective value; Solvable includes the infeasible case; reason: Lean transcription of the conventions stated on p.40; same instances
--   - reading: Definition 1 (iii): fi(xS) < 0 for every nonlinear fi → fi(xS) < 0 for every fi that is not affine; reason: the paper's conic version, Definition A.6 (p.41), says 'with the exception of those for which fi is affine'; the reading 'not homogeneous linear' would strengthen the hypothesis
--   - encoding: vector equations Σ wi = 0 and constraints λ ≥ 0 (ν ≥ 0) in a Slater point (Definition 1) → the scalar linear equations ⟨v, Σ wi⟩ = 0 for all v, and the affine inequalities −λi ≤ 0 (−νiℓ ≤ 0); reason: the same feasible set; all these functions are finite and affine, so conditions (i)–(iii) of Definition 1 are those of the coordinate representation, and strictness gives λ > 0 as in the proof of Proposition C.6 (p.47)
--   - encoding: index sets I, I0 = {0} ∪ I → Fintype ι (possibly empty), with the index 0 carried separately as f₀, w₀; reason: Lean convention; same instances
--   - encoding: convex perspective on ℝ^{dx} × ℝ₊ (Definitions A.2, A.4) → persp/pPersp with value +∞ for t < 0; reason: every multiplier in the paper is ≥ 0; no value at t ≥ 0 changes
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), Theorem 2, pp.7–8

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PWDB_ConvexProgram
import Definitions.Def_PWDB_Slater
import Definitions.Def_PWDB_Solvable

namespace PWDB

/-- **Theorem 2 (Strong Duality)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Theorem 2,
pp.7–8): "The following statements hold.
(i) If (P) or (D) admits a Slater point, then the infimum of (P) coincides with the supremum of
(D), and (D) or (P) is solvable, respectively.
(ii) If the feasible region of (P) or (D) is nonempty and bounded, then the infimum of (P)
coincides with the supremum of (D), and (P) or (D) is solvable, respectively."

The four conjuncts are: (i) for a Slater point of (P), then of (D); (ii) for a nonempty bounded
feasible region of (P), then of (D).

**Formalization Note** (F) is `TensorAHPE.IsProperClosedConvex`; the functions are
extended-valued. A Slater point of (P) is `SlaterMin` (Definition 2) with constraints `fi ≤ 0` and
no equality constraints (`Empty`); affine `fi` are exempt from strictness. A Slater point of (D) is
`SlaterMax` (p.7) on the variable space `E × (I → E) × (I → ℝ)` with the affine inequality
constraints `−λi ≤ 0` (`dIneq`) and the linear equations `Σ wi = 0` (`dEq`). "Solvable" is p.40's
notion, `SolvableMin`/`SolvableMax`, in which an infeasible problem is solvable. Feasible regions
exclude the bad objective value (p.40). -/
theorem theorem_2 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f₀ : E → EReal) (f : ι → E → EReal)
    (hf₀ : TensorAHPE.IsProperClosedConvex f₀) (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i)) :
    ((∃ xS, SlaterMin f₀ f (fun e : Empty => e.elim) xS) →
        pVal f₀ f = dVal f₀ f ∧ SolvableMax (dFeas f₀ f) (dObj f₀ f)) ∧
    ((∃ pS, SlaterMax (dObj f₀ f) (dIneq ι) (dEq ι) pS) →
        pVal f₀ f = dVal f₀ f ∧ SolvableMin (pFeas f₀ f) f₀) ∧
    ((pFeas f₀ f).Nonempty → Bornology.IsBounded (pFeas f₀ f) →
        pVal f₀ f = dVal f₀ f ∧ SolvableMin (pFeas f₀ f) f₀) ∧
    ((dFeas f₀ f).Nonempty → Bornology.IsBounded (dFeas f₀ f) →
        pVal f₀ f = dVal f₀ f ∧ SolvableMax (dFeas f₀ f) (dObj f₀ f)) := by sorry

end PWDB
