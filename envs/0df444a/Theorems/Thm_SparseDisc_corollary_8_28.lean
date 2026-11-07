-- Prove2me | Theorems.Thm_SparseDisc_corollary_8_28
-- name    : SparseDisc.corollary_8_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:39.627723+00:00
-- url     : https://prove2.me/theorems/bd754e47-6a15-4ede-8552-2e1b089d17d9
-- title:
--   Corollary 8.28 — lossless (near-loop) transfer
-- statement:
--   Let $S \ne \emptyset$ and $T$ be disjoint finite sets, let $\ell \ge 1$, and let $Z \subseteq \{\pm1\}^{S \cup T}$ be $\ell$-coarse. Then
--   $$
--   Z^\natural = \{ \rho \in \{\pm1\}^T : \{ s \in \{\pm1\}^S : (s, \rho) \in Z \} \text{ contains a near-loop} \}
--   $$
--   is $\ell$-coarse.
--
--   Compared with the hub transfer (Corollary 8.16), demanding only a near-loop from a neighbour costs it no level; this is what improves the bound $d + 1$ to $\max(2, d)$.
--
--   **Formalization Note** $S \cup T$ is the sum type $S \oplus T$; $T$ may be empty.
--
--   Differences from the source:
--   - encoding: disjoint finite sets S, T and {±1}^{S∪T} → finite types S, T and the cube on the sum type S ⊕ T; reason: Lean convention; disjoint unions are sum types
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Corollary 8.28, p.42

import Mathlib
import Definitions.Def_SparseDisc_IsCoarse
import Definitions.Def_SparseDisc_HasNearLoop

namespace SparseDisc

/-- **Corollary 8.28 (lossless transfer)** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.42). Let `S ≠ ∅` and
`T` be disjoint finite sets, `ℓ ≥ 1`, and `Z ⊆ {±1}^{S ∪ T}` be `ℓ`-coarse. Then
`Z♮ = {ρ ∈ {±1}^T : {s ∈ {±1}^S : (s, ρ) ∈ Z} contains a near-loop}` is `ℓ`-coarse.

**Formalization Note** `S ∪ T` is `S ⊕ T` and `(s, ρ)` is `Sum.elim s ρ`; `T` may be empty. -/
theorem corollary_8_28 {S T : Type} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    [Nonempty S] (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (Z : Set (Cube (S ⊕ T))) (hZ : IsCoarse ℓ Z) :
    IsCoarse ℓ {ρ : Cube T | HasNearLoop {s : Cube S | Sum.elim s ρ ∈ Z}} := by sorry

end SparseDisc
