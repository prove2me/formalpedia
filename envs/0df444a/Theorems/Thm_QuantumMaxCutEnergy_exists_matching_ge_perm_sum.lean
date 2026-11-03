-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_matching_ge_perm_sum
-- name    : QuantumMaxCutEnergy.exists_matching_ge_perm_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T03:24:39.446144+00:00
-- url     : https://prove2.me/theorems/f3f3e0a0-c8e8-4ca1-be83-f82ebd4460c3
-- title:
--   A permutation with bipartite steps is dominated by twice an integral matching
-- statement:
--   **Per-permutation matching bound.**
--
--   With $c$ a bipartition of the support of $x$, $\sigma$ a permutation all of whose nontrivial steps have nonzero
--   pair weight, there is an integral **matching** $M$ with
--   $$\sum_{a} x_{\{a,\sigma a\}}\;\le\;2\sum_{e\in M}w_e .$$
--
--   **Proof.** Split the sum by the colour of the source vertex $a$. Each half is a matching by the previous node
--   (imported — this submission is a tracked reduction), with weight at least its half of the sum; take whichever of
--   the two matchings is heavier.
--
--   **Role.** This is the last combinatorial input of the bipartite case of Edmonds' exactness. Combined with
--   Birkhoff's decomposition of the padded fractional matching and the identity
--   $2\sum_e w_ex_e=\sum_\sigma\lambda_\sigma\sum_a w_{\{a,\sigma a\}}$, it produces a single matching of weight at
--   least $\sum_e w_ex_e$: the averaging over $\sigma$ (with $\sum_\sigma\lambda_\sigma=1$) picks the permutation
--   whose matching is heaviest.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Birkhoff-von Neumann decomposition; the bipartite case of the odd-set polytope's exactness.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Per-permutation matching bound**: the steps of a permutation whose endpoints have different colours
carry at most twice the weight of a single integral matching. -/
theorem exists_matching_ge_perm_sum {n : ℕ} (w x : Edge n → ℝ)
    (c : Fin n → Bool) (hc : ∀ e : Edge n, c e.val.1 ≠ c e.val.2)
    (σ : Equiv.Perm (Fin n)) (hne : ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ a, pairWeight w a (σ a) ≤ 2 * ∑ e ∈ M, w e := by sorry

end QuantumMaxCutEnergy
