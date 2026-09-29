-- Prove2me | Theorems.Thm_Supermodularity_Matching_isIncreasing_of_optimal_of_jointlyStrictlySupermodular
-- name    : Supermodularity.Matching.isIncreasing_of_optimal_of_jointlyStrictlySupermodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:27.354197+00:00
-- url     : https://prove2.me/theorems/52cbabc1-ca66-4880-b97c-e27811d2cf81
-- title:
--   Theorem 3.2.5 — every optimal matching is increasing
-- statement:
--   Suppose $f(x,j)$ is *strictly* supermodular in the joint variable $(x,j)$ on
--   $\bigl(\prod_{i=1}^n X_i\bigr) \times \{1,\dots,m\}$ (with $\{1,\dots,m\}$ ordered as a
--   chain). Then every optimal matching is **increasing** (`IsIncreasingMatching`).
--
--   Topkis, Theorem 3.2.5 (p. 101): "If $f(x,j)$ is strictly supermodular in $(x,j)$ on
--   $\times_{i=1}^n X_i \times \{1,\dots,m\}$, then each optimal matching is increasing." The
--   proof first invokes Theorem 3.2.4 to get that any optimal matching is ordered, then swaps
--   the assignments of any two firms out of order and derives a strict profit improvement from
--   joint strict supermodularity, contradicting optimality. Combined with Theorem 3.2.3, when
--   the labor market is also tight this shows a matching is optimal if and only if it is
--   increasing.
--
--   **Formalization Note.** The hypothesis here — strict supermodularity of the *joint* function
--   $(x,j)\mapsto f(x,j)$ on the product lattice $\bigl(\prod_i X_i\bigr)\times\mathrm{Fin}\,m$
--   — is strictly stronger than, and not to be confused with, Theorem 3.2.4's pair of hypotheses
--   (joint non-strict supermodularity together with strict supermodularity in $x$ alone for each
--   fixed $j$); the two milestones keep their own hypotheses rather than one being stated as a
--   special case of the other.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 101, Theorem 3.2.5

import Mathlib
import Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
import Definitions.Def_Supermodularity_Matching_IsOptimalMatching
import Definitions.Def_Supermodularity_Matching_IsIncreasingMatching

namespace Supermodularity.Matching

theorem isIncreasing_of_optimal_of_jointlyStrictlySupermodular
    {n m : ℕ} {X : Fin n → Type*} [∀ i, Lattice (X i)]
    (f : (∀ i, X i) → Fin m → ℝ)
    (hf : StrictlySupermodularOn (fun p : (∀ i, X i) × Fin m => f p.1 p.2) Set.univ) :
    ∀ x : Fin m → ∀ i, X i, IsOptimalMatching f x → IsIncreasingMatching x := by sorry

end Supermodularity.Matching
