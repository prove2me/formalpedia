-- Prove2me | Theorems.Thm_SymCircMM_lemma_4_4_restricted_outputs_independent
-- name    : SymCircMM.lemma_4_4_restricted_outputs_independent
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:40.780922+00:00
-- url     : https://prove2.me/theorems/093edeee-fd98-4827-9be3-3ce01110fce3
-- title:
--   Lemma 4.4 — the $n^2$ restricted outputs $C^{(i)}_{a,b}$ are linearly independent
-- statement:
--   Let $G\le S_n$ with $\mathrm{char}(F)\nmid|G|$, let $V_i$ be an irreducible constituent of the permutation representation, $U_i$ its isotypic component and $U_{i^*}$ that of $V_{i^*}\simeq V_i^*$. Let $A_i$ be the space of $n\times n$ matrices all of whose rows lie in $U_i$, and $B_i$ the space of matrices all of whose columns lie in $U_{i^*}$. Then the $n^2$ bilinear forms
--
--   $$C^{(i)}_{a,b}(X,Y)=\sum_{j=1}^nX_{a,j}Y_{j,b},\qquad (X,Y)\in A_i\times B_i,\quad (a,b)\in[n]^2,$$
--
--   are linearly independent over $F$.
--
--   Every bilinear circuit for $\mathrm{MM}_n$ must therefore span $n^2$ independent forms on each block $A_i\times B_i$.
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - reading: U_{i*}, the isotypic component of the constituent V_{i*} ≃ V_i^* (the involution i ↦ i*, PDF p.12) → the isotypic component of an irreducible subrepresentation W′ with W′ ≃ W^* (W = V_i); reason: i* is defined by V_{i*} ≃ V_i^*, and the isotypic component depends only on the equivalence class
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
--   - encoding: functions A × B → F → curried functions Matrix ι ι F → Matrix ι ι F → F (restrictions as functions on the product of the subspaces A_i × B_i); reason: Lean convention; the same functions
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma 4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_SymCircMM_util

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma 4.4** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.12 (PDF p.13)): "For every i ≤ r, the n² bilinear forms C^{(i)}_{a,b},
(a, b) ∈ [n]², are linearly independent." Here `C_{a,b}(X, Y) = ∑_j X_{a,j} Y_{j,b}` (4), and
`C^{(i)}_{a,b}` is its restriction to `A_i × B_i`, `A_i` the matrices with every row in `U_i` and `B_i`
the matrices with every column in `U_{i*}`.

**Formalization Note.** `V_i = W` is an irreducible subrepresentation of the permutation
representation and `W′ ≃ W^*` stands for `V_{i*}`; the restrictions are functions on
`A_i × B_i`. The standing assumption `char F ∤ |G|` of §4.2 is included. -/
theorem lemma_4_4_restricted_outputs_independent {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    (W W' : Subrepresentation (permRep F G)) (hW : W.toRepresentation.IsIrreducible)
    (hW' : Nonempty (W'.toRepresentation.Equiv W.toRepresentation.dual)) :
    LinearIndependent F (fun ab : ι × ι =>
      fun p : rowsIn (isotypic W) × colsIn (isotypic W') =>
        mmForm ab.1 ab.2 (p.1 : Matrix ι ι F) (p.2 : Matrix ι ι F)) := by sorry

end SymCircMM
