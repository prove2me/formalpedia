-- Prove2me | Theorems.Thm_StrictCQ_Scaled_Supplement_theorem_5_1
-- name    : StrictCQ.Scaled.Supplement.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T17:56:37.485013+00:00
-- url     : https://prove2.me/theorems/614bae04-2595-44eb-aba7-88adecdb5cc4
-- title:
--   Theorem 5.1 (corrected: clauses 1–3 and refutation of clause 4)
-- statement:
--   Let $h_i,g_j$ be continuously differentiable functions on $\mathbb R^n$, and let $x^*\in\Omega=\{x:h(x)=0,\ g(x)\le0\}$. The first three assertions are
--   $$\begin{aligned}
--   \mathrm{CCP}(x^*)&\Longrightarrow\mathrm{AGP\text{-}regular}(x^*),\\
--   \mathrm{AGP\text{-}regular}(x^*)&\Longrightarrow\mathrm{SAKKT\text{-}regular}(x^*),\\
--   \mathrm{AGP\text{-}regular}(x^*)&\Longrightarrow\mathrm{LAGP\text{-}regular}(x^*).
--   \end{aligned}$$
--   The fourth printed implication is refuted: there exists a continuously differentiable system $D$ on $\mathbb R$, with no equalities and the single inequality $g(x)=-x^2$, for which
--   $$0\in\Omega_D,\qquad\mathrm{SAKKT\text{-}regular}_D(0)\quad\text{and}\quad\neg\mathrm{CAKKT\text{-}regular}_D(0).$$
--   The first three clauses compare the regularity conditions on their entire finite-dimensional domain; the final clause records a counterexample to the remaining printed assertion. These are companion results, not prerequisites for the referenced Scaled-AKKT goal.
--
--   **Formalization Note** All regularity predicates are imported unchanged. The same families $h,g$ are passed to the distinct published AGP, SAKKT and CAKKT structure types. CCP includes both semicontinuity directions. The counterexample is part of this single item, rather than an unmarked companion carrying a missing clause.
--
--   Differences from the source:
--   - reading: the standing C¹ constraints and feasible point → explicit C.IsC1 and xs ∈ C.feasible; reason: these are the governing assumptions on pp. 1, 5 and Definitions 4.1–4.4
--   - correction: SAKKT-regular implies CAKKT-regular (clause 4) → a C¹ feasible counterexample g(x) = −x² at 0 with SAKKT-regularity and failure of CAKKT-regularity; reason: the printed implication is false; DISPROOF.md gives the complete cone and sequence calculation
--   - encoding: one constraint system across four regularity notions → the identical h and g fields in the three published constraint structure types; reason: the carriers and functions agree exactly; no regularity predicate is redefined
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 13, Theorem 5.1 and its proof

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Supplement_CCP
import Definitions.Def_StrictCQ_AGP_LAGP
import Definitions.Def_StrictCQ_SAKKT_Conditions
import Definitions.Def_StrictCQ_CAKKT_Conditions

namespace StrictCQ.Scaled.Supplement

/-- Theorem 5.1, p. 13, corrected: clauses 1–3, together with a counterexample to clause 4.
The counterexample has n = 1, m = 0, p = 1 and g(x) = -x² at the feasible point 0. -/
theorem theorem_5_1 {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hC : C.IsC1) (hxs : xs ∈ C.feasible) :
    (CCP C xs → C.AGPRegular xs) ∧
    (C.AGPRegular xs →
      (⟨C.h, C.g⟩ : StrictCQ.SAKKT.Constraints n m p).SAKKTRegular xs) ∧
    (C.AGPRegular xs → C.LAGPRegular xs) ∧
    (∃ D : StrictCQ.AGP.Constraints 1 0 1,
      (∀ (j : Fin 1) (x : EuclideanSpace ℝ (Fin 1)), D.g j x = -(x 0)^2) ∧
      D.IsC1 ∧ (0 : EuclideanSpace ℝ (Fin 1)) ∈ D.feasible ∧
      (⟨D.h, D.g⟩ : StrictCQ.SAKKT.Constraints 1 0 1).SAKKTRegular 0 ∧
      ¬ (⟨D.h, D.g⟩ : StrictCQ.CAKKT.Constraints 1 0 1).CAKKTRegular 0) := by sorry

end StrictCQ.Scaled.Supplement
