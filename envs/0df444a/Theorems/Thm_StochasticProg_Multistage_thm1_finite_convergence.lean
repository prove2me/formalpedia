-- Prove2me | Theorems.Thm_StochasticProg_Multistage_thm1_finite_convergence
-- name    : StochasticProg.Multistage.thm1_finite_convergence
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:10:30.690719+00:00
-- url     : https://prove2.me/theorems/7cf4cf2b-be09-45b8-aeb7-f08fd8c8cf89
-- title:
--   Chapter 6, Theorem 1 — finite convergence of the nested L-shaped method
-- statement:
--   Birge & Louveaux, Chapter 6, Theorem 1 (p. 268 / PDF p. 289): "If all $\Xi_t$ are finite
--   and all $x_t$ have finite upper bounds, then the nested L-shaped method converges finitely
--   to an optimal solution of (3.4.1)."
--
--   Formalized as: starting from no cuts at all (`path 0 = (∅, ∅)`), every run of the
--   algorithm's Step-1/2 transition (`Step`) reaches, within a number of steps bounded by the
--   finite total number of feasibility- and optimality-cut witnesses available on the tree
--   ($|\mathrm{Node}\times\mathrm{FeasBasis}| + |\mathrm{Node}\to\mathrm{Basis}|$, generalizing
--   Chapter 5's finite-basis bound to the tree, node by node), a state from which no further
--   `Step` cut can be added. At that state, either the root's local master problem has become
--   infeasible (certifying the tree-wide problem (3.4.1) infeasible) or there is a tree-wide
--   assignment $x,\theta$ that is jointly Step-1-optimal at every node, is feasible for
--   (3.4.1), satisfies every fresh Step-3 termination test at every node with children, and is
--   optimal for (3.4.1) among all feasible tree-wide assignments.
--
--   "All $\Xi_t$ finite" is built into `Node` being a `Fintype`; "$x_t$ have finite upper
--   bounds" is `ub` being `ℝ`-valued (`Def_StochasticProg_Multistage_Instance`).
--
--   **Formalization Note.** The book's own proof of this theorem (p. 290) is an induction on
--   $t$ reducing to the two-stage method's finite convergence (Chapter 5, Theorem 2) for the
--   base case; there is no separately numbered lemma before Theorem 1 in the chapter to draft
--   as an independent milestone (see `STATUS.md`), and Chapter 5's Theorem 2 is itself an
--   unpublished draft in this series, so it cannot be cited as a `reference` item.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 268, Chapter 6, Theorem 1 (PDF p. 289)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_Multistage_Instance
import Definitions.Def_StochasticProg_Multistage_Bases
import Definitions.Def_StochasticProg_Multistage_Algorithm

namespace StochasticProg.Multistage

open scoped Matrix

variable {H n m : ℕ} {T : Tree H}

/-- Chapter 6, Theorem 1 (p. 268 / PDF p. 289): "If all `Ξ_t` are finite and all `x_t` have
finite upper bounds, then the nested `L`-shaped method converges finitely to an optimal
solution of (3.4.1)."

Formalized as: starting from no cuts at all, every run of the algorithm's Step-1/2
transition (`Step`) reaches, within a number of steps bounded by the finite total number of
feasibility- and optimality-cut witnesses available on the tree
(`Fintype.card (T.Node × FeasBasis n m) + Fintype.card (T.Node → Basis n m)`, generalizing
Chapter 5's finite-basis bound, p. 220, node by node), a state from which no further `Step`
cut can be added, i.e. either the root's local master problem has become infeasible
(certifying the tree-wide problem (3.4.1) infeasible) or a tree-wide assignment `x` is
jointly Step-1-optimal at every node, satisfies every fresh Step-3 termination test at every
node with children, is feasible for (3.4.1), and is optimal for (3.4.1). `Ξ_t` finite is
built into `T.Node` being a `Fintype`; "`x_t` have finite upper bounds" is `inst.ub` being
`ℝ`-valued. -/
theorem thm1_finite_convergence (inst : Instance H n m T) :
    ∃ (N : ℕ) (path : ℕ → State inst),
      N ≤ Fintype.card (T.Node × FeasBasis n m) + Fintype.card (T.Node → Basis n m) ∧
      path 0 = (∅, ∅) ∧
      (∀ i, i < N → Step inst (path i) (path (i + 1))) ∧
      (∀ Sf' So', ¬ Step inst (path N) (Sf', So')) ∧
      ((IsRootInfeasible inst (path N).1 ∧ ¬ ∃ x, Feasible inst x) ∨
        (∃ x : T.Node → Fin n → ℝ, ∃ θ : T.Node → ℝ,
          (∀ j, IsNodeOptimal inst (path N).1 (path N).2 j
              (if (T.stage j).val = 0 then 0 else x (T.anc j)) (x j) (θ j)) ∧
          Feasible inst x ∧
          (∀ j, (T.children j).Nonempty → ∀ β : T.Node → Basis n m,
            (∀ k ∈ T.children j, IsOptimalAt inst k (β k) (x j)) →
            θ j ≥ (optCutCoeffs inst β j).2 - dotProduct (optCutCoeffs inst β j).1 (x j)) ∧
          ∀ x' : T.Node → Fin n → ℝ, Feasible inst x' → obj inst x ≤ obj inst x')) := by sorry

end StochasticProg.Multistage
