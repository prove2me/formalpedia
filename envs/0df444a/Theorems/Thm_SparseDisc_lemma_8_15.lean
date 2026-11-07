-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_15
-- name    : SparseDisc.lemma_8_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:31.199064+00:00
-- url     : https://prove2.me/theorems/8f1ea59a-27b8-4eac-b4c6-9ed54eb893f9
-- title:
--   Lemma 8.15 — hub transfer
-- statement:
--   Let $S \ne \emptyset$ and $T$ be disjoint finite sets, let $\psi : \{\pm1\}^{S \cup T} \to \mathbb R$ be odd and 2-Lipschitz, let $a \ge 0$, and let $\rho_0, \dots, \rho_L$ be an antipodal $a$-path in $\{\pm1\}^T$.
--
--   1. If $T \ne \emptyset$, then for some $\tau \in \{0, \dots, L\}$ the set
--   $$
--   W(\rho_\tau) = \{ s \in \{\pm1\}^S : |\psi(s, \rho_\tau)| \le a + 1 \}
--   $$
--   contains a 1-loop.
--   2. If $T = \emptyset$, then $\{ s \in \{\pm1\}^S : |\psi(s)| \le 2 \}$ contains a 1-loop.
--
--   When a vertex of the pattern is deleted, the lemma lets each neighbour keep a constraint of the same type, one level lower, that leaves room for a 1-loop of the shared bundle.
--
--   **Formalization Note** $S \cup T$ is the disjoint union $S \oplus T$ and $(s, \rho)$ is the concatenation. Part 2 is stated directly for odd 2-Lipschitz functions on $\{\pm1\}^S$.
--
--   Differences from the source:
--   - encoding: disjoint finite sets S, T and {±1}^{S∪T} → finite types S, T and the cube on the sum type S ⊕ T; reason: Lean convention; disjoint unions are sum types
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.15, p.34

import Mathlib
import Definitions.Def_SparseDisc_IsOdd
import Definitions.Def_SparseDisc_IsLip
import Definitions.Def_SparseDisc_HasLoop

namespace SparseDisc

/-- **Lemma 8.15 (hub transfer)** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.34). Let `S ≠ ∅` and `T` be
disjoint finite sets, `ψ : {±1}^{S ∪ T} → ℝ` odd and 2-Lipschitz, `a ≥ 0`, and `ρ₀, …, ρ_L` an
antipodal `a`-path in `{±1}^T`. If `T ≠ ∅`, then for some `τ` the set
`W(ρ_τ) = {s ∈ {±1}^S : |ψ(s, ρ_τ)| ≤ a + 1}` contains a 1-loop. If `T = ∅`, then
`{s ∈ {±1}^S : |ψ(s)| ≤ 2}` contains a 1-loop.

**Formalization Note** The disjoint union `S ∪ T` is the sum type `S ⊕ T` and `(s, ρ)` is
`Sum.elim s ρ`. The case `T = ∅` is stated directly for odd 2-Lipschitz `ψ` on `{±1}^S`. -/
theorem lemma_8_15 {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    [Nonempty S] :
    (∀ (ψ : Cube (S ⊕ T) → ℝ), IsOdd ψ → IsLip 2 ψ → ∀ (a : ℝ), 0 ≤ a →
      ∀ (ρ : ℕ → Cube T) (L : ℕ), IsSPath a Set.univ ρ L → ρ L = -(ρ 0) → Nonempty T →
        ∃ τ ≤ L, HasLoop 1 {s : Cube S | |ψ (Sum.elim s (ρ τ))| ≤ a + 1}) ∧
    (∀ (ψ : Cube S → ℝ), IsOdd ψ → IsLip 2 ψ → HasLoop 1 {s : Cube S | |ψ s| ≤ 2}) := by sorry

end SparseDisc
