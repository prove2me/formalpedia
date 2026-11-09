-- Prove2me | Theorems.Thm_SharpPauliEntanglement_Exact_symmetrized_product_cancellation
-- name    : SharpPauliEntanglement.Exact.symmetrized_product_cancellation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:46.47112+00:00
-- url     : https://prove2.me/theorems/f3759faf-bccd-4684-8736-67316e902aab
-- title:
--   Lemma 3.4 — Full 1/3 Pauli-norm bound for lists with repetitions and an anticommuting pair
-- statement:
--   Let $S_1,\ldots,S_M$ be signed Hermitian Pauli strings on $n$ qubits, allowing repetitions. Define $\operatorname{Sym}$ as the average of the ordered products over all $M!$ permutations of occurrence slots. If two distinct slots contain an anticommuting pair, then
--
--   $$\left\|\operatorname{Sym}(S_1,\ldots,S_M)\right\|_{P,1}\le\frac13.$$
--
--   The bound is the exact cancellation constant used to control noncommuting inclusion-exclusion terms. Repeated equal strings remain separate slots in the average.
--
--   Differences from the source:
--   - encoding: arbitrary finite qubit and term labels → computational bitstrings and Fin n, Fin m labels; reason: finite reindexing preserves every matrix, support relation and source instance
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), printed/PDF p. 11, Lemma 3.4

import Definitions.Def_SharpPauliEntanglement_Exact_PauliModel

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Kiani, p. 11, Lemma 3.4. Signed strings and repeated slots are permitted. -/
theorem symmetrized_product_cancellation {n M : ℕ} (S : Fin M → SignedPauli (Fin n))
    (hanti : ∃ i j, i ≠ j ∧ signedOp (S i) * signedOp (S j) =
      -(signedOp (S j) * signedOp (S i))) :
    pauliNorm (symmetrizedProduct S) ≤ (1 / 3 : ℝ) := by sorry

end SharpPauliEntanglement.Exact
