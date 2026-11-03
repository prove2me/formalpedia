-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_matching_ge_color_sum
-- name    : QuantumMaxCutEnergy.exists_matching_ge_color_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T03:24:54.194473+00:00
-- url     : https://prove2.me/theorems/31ae9b19-2564-4e99-bc1a-94ce2328f91a
-- title:
--   Steps of a permutation inside one colour class form a matching of the same weight
-- statement:
--   **One colour class of a permutation's steps is a matching.**
--
--   Let $x\ge0$ be an edge weight on a graph whose edges all join *different* colour classes of a colouring
--   $c:V\to\{\text{false},\text{true}\}$ (so $c$ is a bipartition of the support), let $\sigma$ be a permutation of
--   the vertex set, and suppose every nontrivial step of $\sigma$ has a *nonzero* pair weight
--   ($x_{\{a,\sigma a\}}\neq0$ whenever $\sigma a\neq a$). Then, for either colour $b$, the edges
--   $\{a,\sigma a\}$ over the vertices $a$ with $c(a)=b$ and $\sigma a\neq a$ form a **matching**, and
--   $$\sum_{a:\,c(a)=b,\,\sigma a\ne a} x_{\{a,\sigma a\}}\;\le\;\sum_{e\in M}w_e .$$
--
--   **Why it is a matching.** Two such edges sharing a vertex $v$ would have $v=a=a'$ (both vertices of colour
--   $b$; then $a=a'$) or $v=\sigma a=\sigma a'$ (both of the other colour; then $a=a'$ by injectivity), or one
--   $b$-vertex equal to one non-$b$-vertex, which is impossible. The nonzero-weight hypothesis is what forces
--   $\sigma a$ to have the *other* colour, via the bipartition of the support.
--
--   **Role.** This is the substitute for the "alternating even cycle" argument in the bipartite case of Edmonds'
--   exactness: instead of decomposing a permutation into cycles and taking alternate edges, split by the colour of
--   the *source* of each step. The two halves are matchings and their weights add up to the total step weight, so
--   the total is at most twice the better one — exactly the factor that cancels against the $2$ in
--   $2\sum_e w_ex_e=\sum_\sigma\lambda_\sigma\sum_a w_{\{a,\sigma a\}}$.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the colour-splitting replaces the even-cycle decomposition in the bipartite case of the matching-polytope theorem.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The steps of a permutation that start in one colour class form a matching of the same total weight. -/
theorem exists_matching_ge_color_sum {n : ℕ} (w : Edge n → ℝ) (x : Edge n → ℝ)
    (c : Fin n → Bool) (hc : ∀ e : Edge n, c e.val.1 ≠ c e.val.2)
    (σ : Equiv.Perm (Fin n)) (b : Bool)
    (hne : ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ a ∈ Finset.univ.filter (fun a : Fin n => c a = b ∧ σ a ≠ a), pairWeight w a (σ a))
        ≤ ∑ e ∈ M, w e := by sorry

end QuantumMaxCutEnergy
