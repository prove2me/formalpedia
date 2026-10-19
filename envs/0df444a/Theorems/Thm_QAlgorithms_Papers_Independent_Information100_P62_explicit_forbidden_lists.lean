-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_explicit_forbidden_lists
-- name    : QAlgorithms.Papers.Independent.Information100.P62.explicit_forbidden_lists
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:47:25.133436+00:00
-- url     : https://prove2.me/theorems/ec95089d-e02c-4ce5-814a-1fe98941c145
-- title:
--   Table 1: explicit forbidden lists
-- statement:
--   The minimal forbidden lists are
--   $$F(M_d)=\{\mathbb C^{d+1}\}\ (d\ge1),\qquad F(\mathbb C^c)=\{M_2,\mathbb C^{c+1}\}\ (c\ge2).$$
--   Further, $F(M_2\oplus\mathbb C)=\{M_3,\mathbb C^4\}$, $F(M_3\oplus\mathbb C)=\{M_2\oplus M_2,\mathbb C^5\}$, $F(M_3\oplus M_2)=\{M_4,\mathbb C^6\}$, and $F(M_4\oplus\mathbb C)=\{M_3\oplus M_2,\mathbb C^6\}$. In particular $F(\mathbb C)=\{\mathbb C^2\}$. All matrix algebras are over $\mathbb C$, and sums are algebra direct sums. These are explicit finite domination tests.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 38, Table 1: explicit forbidden lists

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.38, Table 1: explicit forbidden lists. -/
theorem explicit_forbidden_lists :
    (∀ d : ℕ, 1 ≤ d → forbidden (quantum d) = {classical (d + 1)}) ∧
    (∀ c : ℕ, 2 ≤ c → forbidden (classical c) = {quantum 2, classical (c + 1)}) ∧
    forbidden (quantum 2 + quantum 1) = {quantum 3, classical 4} ∧
    forbidden (quantum 3 + quantum 1) = {equalBlocks 2 2, classical 5} ∧
    forbidden (quantum 3 + quantum 2) = {quantum 4, classical 6} ∧
    forbidden (quantum 4 + quantum 1) = {quantum 3 + quantum 2, classical 6} ∧
    forbidden (quantum 1) = {classical 2} := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
