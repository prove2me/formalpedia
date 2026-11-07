-- Prove2me | Theorems.Thm_SymCircMM_proposition_2_11_abelian_transitive_subgroups
-- name    : SymCircMM.proposition_2_11_abelian_transitive_subgroups
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:30:35.43537+00:00
-- url     : https://prove2.me/theorems/aca30660-79f4-4d11-911d-a6b16ea8a0c3
-- title:
--   Proposition 2.11 — $C_n$ and $(C_2)^k$ are abelian transitive subgroups of $G_k$
-- statement:
--   Let $n=2^k$. The group $G_k=\mathrm{Aut}(T_k)$, acting on the leaves $\{0,1\}^k$, contains two abelian subgroups acting transitively on the leaves:
--
--   1. $C_n$, a cyclic group of order $n$;
--   2. $(C_2)^k$, an elementary abelian $2$-group of order $n$.
--
--   Through Corollary 4.10 either subgroup gives the cubic lower bound for $G_k$-symmetric circuits.
--
--   **Formalization Note** The subgroups are subgroups of `treeAut k`; the first is cyclic with $2^k$ elements, the second is isomorphic to $(\mathbb Z/2)^k$; commutativity and transitivity on the leaves are stated for both.
--
--   Differences from the source:
--
--   - encoding: [n] identified with the leaves {0,1}^k of T_k, and G_k = Aut(T_k) acting faithfully on the leaves → Leaf k = Fin k → Bool and treeAut k, the permutations of the leaves that preserve, for every depth i ≤ k, the relation "below the same node of depth i"; reason: these are exactly the leaf permutations induced by automorphisms of T_k (which permute the leaf sets L(v), PDF p.7), and the induced action is faithful
--   - encoding: C_n, the cyclic group of order n, and (C_2)^k → a cyclic subgroup H₁ with Nat.card H₁ = 2^k, and a subgroup H₂ with H₂ ≃* Multiplicative (Fin k → ZMod 2); reason: the definitions of these groups up to isomorphism
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), Proposition 2.11, p.5 (PDF p.6); proof Appendix A, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_SymCircMM_treeAut

set_option autoImplicit false

namespace SymCircMM

/-- **Proposition 2.11** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.5 (PDF p.6); proof Appendix A, p.15 (PDF p.16)): "G_k contains two
abelian subgroups acting transitively on the set of leaves: C_n, the cyclic group of order n, and
(C_2)^k."

**Formalization Note.** Both subgroups are subgroups of `G_k = treeAut k` inside the permutations of
the leaves `{0,1}^k`; `C_n` is a cyclic subgroup of order `n = 2^k`, `(C_2)^k` a subgroup isomorphic to
`(ℤ/2)^k`; commutativity and transitivity on the leaves are stated for both. -/
theorem proposition_2_11_abelian_transitive_subgroups (k : ℕ) :
    ∃ H₁ H₂ : Subgroup (Equiv.Perm (Leaf k)), H₁ ≤ treeAut k ∧ H₂ ≤ treeAut k ∧
      IsCyclic H₁ ∧ Nat.card H₁ = 2 ^ k ∧ Nonempty (H₂ ≃* Multiplicative (Fin k → ZMod 2)) ∧
      (∀ a ∈ H₁, ∀ b ∈ H₁, a * b = b * a) ∧ (∀ a ∈ H₂, ∀ b ∈ H₂, a * b = b * a) ∧
      (∀ i j : Leaf k, ∃ g ∈ H₁, g i = j) ∧ (∀ i j : Leaf k, ∃ g ∈ H₂, g i = j) := by sorry

end SymCircMM
