-- Prove2me | Theorems.Thm_SymCircMM_lemma_4_3_isotypic_pairing
-- name    : SymCircMM.lemma_4_3_isotypic_pairing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:39.577184+00:00
-- url     : https://prove2.me/theorems/a4c77e1b-6878-4a49-a5a4-eeb8d0f12bb6
-- title:
--   Lemma 4.3 — $\langle U_i,U_j\rangle=0$ for $j\ne i^*$, and $\langle\cdot,\cdot\rangle$ is nondegenerate on $U_i\times U_{i^*}$
-- statement:
--   Let $G\le S_n$ with $\mathrm{char}(F)\nmid|G|$, let $V=F^n$ be the permutation representation with the form $\langle x,y\rangle=\sum_jx_jy_j$, and let $U_i$ be the isotypic component of its irreducible constituent $V_i$; let $V_{i^*}\simeq V_i^*$. Then:
--
--   1. if $j\ne i^*$, then $\langle U_i,U_j\rangle=0$;
--   2. the restriction of $\langle\cdot,\cdot\rangle$ to $U_i\times U_{i^*}$ is nondegenerate;
--   3. in particular, for every nonzero $u\in U_i$ there is $w\in U_{i^*}$ with $\langle u,w\rangle\ne0$.
--
--   This lemma explains why the dual index appears on the $B$-side: it is the only pairing of isotypic components on which the outputs $C_{a,b}$ do not vanish.
--
--   **Formalization Note** $V_i=W$ and $V_j=W'$ are irreducible subrepresentations of $V$, "$j\ne i^*$" means that $W'$ is not equivalent to the dual $W^*$, and "$j=i^*$" means $W'\simeq W^*$. Nondegeneracy is stated as trivial left and right kernels.
--
--   Differences from the source:
--
--   - encoding: the index set [n] = {1, …, n} → a finite type ι with n = card ι; reason: a relabelling of the index set
--   - reading: U_{i*}, the isotypic component of the constituent V_{i*} ≃ V_i^* (the involution i ↦ i*, PDF p.12) → the isotypic component of an irreducible subrepresentation W′ with W′ ≃ W^* (W = V_i); reason: i* is defined by V_{i*} ≃ V_i^*, and the isotypic component depends only on the equivalence class
--   - encoding: char(F) ∤ |G| → (Nat.card G : F) ≠ 0; reason: a prime p divides m iff (m : F) = 0 in characteristic p, and (m : F) ≠ 0 for every m ≥ 1 in characteristic 0
--   - encoding: the restriction of ⟨·,·⟩ to U_i × U_{i*} is nondegenerate → trivial left kernel and trivial right kernel of ⟨·,·⟩ on U(W) × U(W′); reason: the definition of nondegeneracy
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Lemma 4.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_SymCircMM_permRep

set_option autoImplicit false

namespace SymCircMM

/-- **Lemma 4.3** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.11 (PDF p.12)): "If j ≠ i* then ⟨U_i, U_j⟩ = 0. The restriction of ⟨·,·⟩
to U_i × U_{i*} is nondegenerate. In particular, for every nonzero u ∈ U_i there is w ∈ U_{i*} with
⟨u, w⟩ ≠ 0." Here `G ≤ S_n` with `char F ∤ |G|`, `U_i` is the isotypic component of the irreducible
constituent `V_i` of the permutation representation `V = F^n`, and `V_{i*} ≃ V_i^*`.

**Formalization Note.** `V_i = W` and `V_j = W′` are irreducible subrepresentations of `V`; "`j ≠ i*`" is
"`W′` is not equivalent to the dual of `W`", and "`j = i*`" is "`W′ ≃ W^*`". Nondegeneracy on
`U(W) × U(W′)` is stated as trivial left and right kernels. -/
theorem lemma_4_3_isotypic_pairing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (Equiv.Perm ι)) (hG : (Nat.card G : F) ≠ 0)
    (W W' : Subrepresentation (permRep F G)) (hW : W.toRepresentation.IsIrreducible)
    (hW' : W'.toRepresentation.IsIrreducible) :
    (IsEmpty (W'.toRepresentation.Equiv W.toRepresentation.dual) →
        ∀ x ∈ isotypic W, ∀ y ∈ isotypic W', dotForm x y = 0) ∧
    (Nonempty (W'.toRepresentation.Equiv W.toRepresentation.dual) →
        (∀ x ∈ isotypic W, (∀ y ∈ isotypic W', dotForm x y = 0) → x = 0) ∧
        (∀ y ∈ isotypic W', (∀ x ∈ isotypic W, dotForm x y = 0) → y = 0)) ∧
    (Nonempty (W'.toRepresentation.Equiv W.toRepresentation.dual) →
        ∀ u ∈ isotypic W, u ≠ 0 → ∃ w ∈ isotypic W', dotForm u w ≠ 0) := by sorry

end SymCircMM
