-- Prove2me | Theorems.Thm_RegMatroidXC_Main_trivial_bound
-- name    : RegMatroidXC.Main.trivial_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:28.871592+00:00
-- url     : https://prove2.me/theorems/a473d12d-4f4e-419d-83f3-10d6fb4c1f87
-- title:
--   Trivial bound (proof of Theorem 1, p. 4) — xc(P(M)) ≤ 2ⁿ
-- statement:
--   For every matroid $M$ on a finite ground set of $n$ elements, the independence polytope $P(M) \subseteq \mathbb R^{E(M)}$ has an extended formulation with at most $2^n$ inequalities:
--   $$\mathrm{xc}(P(M)) \le 2^n .$$
--
--   The proof of the main theorem uses this bound for $M \cong R_{10}$ and for the finitely many small values of $n$ where the inductive estimate does not yet apply.
--
--   **Formalization Note** Stated as the existence of an extended formulation of size at most $2^n$; it holds for every matroid, which is what "trivial" refers to.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 4, proof of Theorem 1

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_RegMatroidXC_Main_Matroids
open ExtensionComplexity.TSP

namespace RegMatroidXC.Main

theorem trivial_bound (α : Type) (M : Matroid α) [Fintype M.E] :
    ∃ r : ℕ, IsEFOfSize (indepPolytope M) r ∧ r ≤ 2 ^ Fintype.card M.E := by sorry

end RegMatroidXC.Main
