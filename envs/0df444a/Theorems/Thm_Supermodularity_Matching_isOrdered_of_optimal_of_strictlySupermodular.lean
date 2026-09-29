-- Prove2me | Theorems.Thm_Supermodularity_Matching_isOrdered_of_optimal_of_strictlySupermodular
-- name    : Supermodularity.Matching.isOrdered_of_optimal_of_strictlySupermodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:22:51.976985+00:00
-- url     : https://prove2.me/theorems/725b15cb-cbc3-4ad4-b658-53ee454ebcc0
-- title:
--   Theorem 3.2.4 — every optimal matching is ordered
-- statement:
--   Suppose $f(x,j)$ is supermodular in the joint variable $(x,j)$ on $\bigl(\prod_{i=1}^n
--   X_i\bigr) \times \{1,\dots,m\}$, and, for each fixed firm $j$, $f(\cdot,j)$ is *strictly*
--   supermodular in $x$ on $\prod_{i=1}^n X_i$. Then every optimal matching is **ordered**
--   (`IsOrderedMatching`): any two of the $m$ quality vectors it assigns are comparable.
--
--   Topkis, Theorem 3.2.4 (p. 100): "If $f(x,j)$ is supermodular in $(x,j)$ on $\times_{i=1}^n
--   X_i \times \{1,\dots,m\}$ and is strictly supermodular in $x$ on $\times_{i=1}^n X_i$ for
--   each $j$, then each optimal matching is ordered." The proof exchanges the assignments of any
--   two unordered firms via $\vee,\wedge$ and derives a strict profit improvement from the two
--   supermodularity hypotheses together, contradicting optimality.
--
--   **Formalization Note.** The two supermodularity hypotheses are genuinely different in kind
--   (joint, non-strict, in $(x,j)$; and per-firm, strict, in $x$ alone) and are kept as two
--   separate hypotheses rather than merged into one strengthened statement, matching the book's
--   own remark that this pair is equivalent to "$f(x,j)$ has increasing differences in $(x,j)$
--   and is strictly supermodular in $x$" by Theorems 2.6.1–2.6.2.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 100, Theorem 3.2.4

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsOrderedMatching

namespace Supermodularity.Matching

theorem isOrdered_of_optimal_of_strictlySupermodular
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : Supermodularity.Monotonicity.SupermodularOn
      (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ)
    (hfx : ∀ j : Fin m, StrictlySupermodularOn (fun x : ∀ i, X i => f x j) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsOrderedMatching x := by sorry

end Supermodularity.Matching
