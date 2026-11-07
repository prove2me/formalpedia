-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_pin
-- name    : SymBoolPCSP.CFixing.polOf_ham_pin
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:39:42.143296+00:00
-- url     : https://prove2.me/theorems/9ea6c5c6-a02e-4156-81b6-f9176a25671c
-- title:
--   Pinning coordinates of Hamming promise relations (iterated Claims 4.2 and 4.4)
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ be idempotent and folded. Let $n, i, j \ge 0$ and $S \subseteq T \subseteq \{0, 1, \dots, n+j+i\}$. If $f$ is a polymorphism of the promise relation $(\mathrm{Ham}_{n+j+i}(S), \mathrm{Ham}_{n+j+i}(T))$, then $f$ is also a polymorphism of
--
--   $$
--   \big(\mathrm{Ham}_n(S'), \mathrm{Ham}_n(T')\big), \qquad S' = \{\ell \le n : \ell + j \in S\}, \quad T' = \{\ell \le n : \ell + j \in T\}.
--   $$
--
--   Combinatorially, this fixes $j$ coordinates to $1$ and $i$ further coordinates to $0$. The proof iterates Claim 4.2 of Brakensiek–Guruswami $i$ times (fixing a coordinate to $0$ removes the top weight and lowers the arity) and Claim 4.4 $j$ times (fixing a coordinate to $1$ shifts all weights down by one). Every reduction to a smaller Hamming promise relation in §4 of the paper (Lemmas 4.5, 4.7, 4.10) is an instance of this one statement.
--
--   **Formalization Note** The arity is written as `n + j + i` so that the iterated statements are definitionally aligned. Use `obtain ⟨i, rfl⟩ : ∃ i, k = n + j + i` to apply the result to a given arity `k`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.1, Claims 4.2 and 4.4, p. 16, as used in the proofs of Lemmas 4.5 and 4.7

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Pinning coordinates of Hamming promise relations (Claims 4.2 and 4.4 iterated): for an idempotent folded `f`, if `f ∈ Pol(Ham_{n+j+i}(S), Ham_{n+j+i}(T))` with `S ⊆ T ⊆ {0,…,n+j+i}`, then `f ∈ Pol(Ham_n(S'), Ham_n(T'))` where `S' = {l ≤ n : l + j ∈ S}` and `T' = {l ≤ n : l + j ∈ T}` (fix `j` coordinates to `1` and `i` coordinates to `0`). -/
theorem polOf_ham_pin {n i j L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic (n + j + i))
    (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham (n + j + i) S) (Ham (n + j + i) T) f) :
    PolOf (Ham n {l | l + j ∈ S ∧ l ≤ n}) (Ham n {l | l + j ∈ T ∧ l ≤ n}) f := by sorry

end SymBoolPCSP.CFixing
