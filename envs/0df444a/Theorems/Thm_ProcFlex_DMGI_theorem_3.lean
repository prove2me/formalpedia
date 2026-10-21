-- Prove2me | Theorems.Thm_ProcFlex_DMGI_theorem_3
-- name    : ProcFlex.DMGI.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:31.62239+00:00
-- url     : https://prove2.me/theorems/a6db10da-e347-4063-bc5a-0796fccdd627
-- title:
--   Theorem 3: worst-case optimality of the alternate long chain
-- statement:
--   Take a balanced system of $2k$ unit-capacity plants and $2k$ products, where $k\ge1$ and exactly $k$ products have each of two positive margins $P_L<P_H$. Let $\mathrm{AL}$ be any chain alternating high- and low-margin products, and let $L_{HL}$ be any long chain on the same products. For every nonempty compact part-wise independently symmetric set $U$ of nonnegative demands and every robust measure $R^f$ in the paper's class $\Gamma$,
--
--   $$
--   R^f(\mathrm{AL},U)\ge R^f(L_{HL},U).
--   $$
--
--   Thus alternating the two margin classes maximizes worst-case performance within the balanced long-chain family, across the stated class of scores and demand sets.
--
--   **Formalization Note** Products and margin categories are fixed while their cyclic order varies. The score is continuous in nonnegative demand for every design, as assumed in §2.2. Nonempty compact $U$ and positive margins are disclosed conditions needed for a well-posed real minimum and the model's profit interpretation.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 21, Theorem 3

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Theorem 3, p. 21: the alternate long chain has the best worst-case
performance among balanced two-margin long chains for every measure in Γ. -/
theorem theorem_3 (k : ℕ) (hk : 1 ≤ k)
    (S : System (2 * k) (2 * k) 2) (hS : S.IsValid)
    (hC : ∀ j, S.C j = 1) (hcard : (S.s 1).card = k)
    (h : ℝ → (Fin 2 → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont : ∀ A : Design (2 * k) (2 * k),
      ContinuousOn (f S h A) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin (2 * k) → ℝ)) (hU : IsPartwiseIndepSymmetric S U)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U)
    (πAL π : Equiv.Perm (Fin (2 * k))) (hAL : IsAlternate S πAL) :
    Rf S h (longChain π) U ≤ Rf S h (longChain πAL) U := by sorry

end ProcFlex.DMGI
