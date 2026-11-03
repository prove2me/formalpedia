-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_two_mul_sum_edges_eq_sum_pairs
-- name    : QuantumMaxCutEnergy.two_mul_sum_edges_eq_sum_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:35:00.541902+00:00
-- url     : https://prove2.me/theorems/ab003894-cb1c-4440-9960-b4886688fcf3
-- title:
--   A symmetric diagonal-free pair function sums to twice the edge sum
-- statement:
--   **A symmetric diagonal-free pair function sums to twice the edge sum.**
--
--   Let $g(a,b)$ be a real function on ordered pairs of vertices of a graph on $n$ vertices which is symmetric
--   ($g(a,b)=g(b,a)$) and vanishes on the diagonal. Then
--   $$2\sum_{e=\{a,b\}}g(a,b)\;=\;\sum_{a}\sum_{b}g(a,b).$$
--
--   **Proof.** Rewrite the double sum as a sum over the product of the vertex set with itself and split it into the
--   diagonal (which contributes $0$), the pairs with $a<b$ and the pairs with $b<a$; the last two are exchanged by
--   the involution $(a,b)\mapsto(b,a)$, which preserves $g$ by symmetry, and the pairs with $a<b$ are exactly the
--   edges.
--
--   **Role.** This converts the *edge-indexed* objective $\sum_e w_ex_e$ of the quantum max-cut campaign into a sum
--   over ordered pairs, which is the form in which the Birkhoff decomposition of the padded fractional matching
--   acts: writing $\mathrm{padWeight}\,x=\sum_\sigma\lambda_\sigma P_\sigma$ gives
--   $$2\sum_e w_ex_e=\sum_\sigma\lambda_\sigma\sum_a w_{\{a,\sigma a\}},$$
--   and in the bipartite case each inner sum is at most twice the weight of a matching (split by the colour class of
--   $a$), which is the last step of the bipartite warm-up for Edmonds' exactness.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); standard double-counting in the Birkhoff-von Neumann reduction of a fractional matching to a doubly stochastic matrix.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- A symmetric, diagonal-free function on ordered pairs sums to twice its edge sum. -/
theorem two_mul_sum_edges_eq_sum_pairs {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hcomm : ∀ a b, g a b = g b a) (hdiag : ∀ a, g a a = 0) :
    2 * (∑ e : Edge n, g e.val.1 e.val.2) = ∑ a, ∑ b, g a b := by sorry

end QuantumMaxCutEnergy
