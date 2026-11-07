-- Prove2me | Theorems.Thm_SparseDisc_lemma_8_29
-- name    : SparseDisc.lemma_8_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:03.858553+00:00
-- url     : https://prove2.me/theorems/65951818-ad99-451e-bd03-48cb3fc530e5
-- title:
--   Lemma 8.29 — cheap deletion
-- statement:
--   Let $(G, \ell)$ be a leveled graph on a finite vertex set, $h$ a vertex, and $J \subseteq N_G(h)$ with $|J| \le \ell_h$, where $\ell_h \ge 2$ if $J \ne \emptyset$, such that every vertex of $N_G(h) \setminus J$ has level at least $2$. Let $\ell'$ lower the levels of the vertices of $N_G(h) \setminus J$ by one. If $(G - h, \ell')$ is good, then $(G, \ell)$ is good.
--
--   A deleted vertex of level $\ell_h$ can thus make up to $\ell_h$ of its neighbours "cheap" (they keep their level), and every further neighbour pays one level.
--
--   **Formalization Note** Levels are natural numbers with $\ell_v \ge 1$ for all $v$ (a hypothesis); $G - h$ is the induced subgraph on the vertices other than $h$; the lowered level $\ell_v - 1$ is applied only to vertices of level at least $2$.
--
--   Differences from the source:
--   - encoding: levels ℓ : V → {1, 2, …} → levels ℓ : V → ℕ with the hypothesis ∀ v, 1 ≤ ℓ v; reason: Lean convention; same leveled graphs
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 8.29, p.42

import Mathlib
import Definitions.Def_SparseDisc_IsLevelGood

namespace SparseDisc

open Classical in
/-- **Lemma 8.29 (cheap deletion)** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.42). Let `(G, ℓ)` be a
leveled graph, `h` a vertex, and `J ⊆ N_G(h)` with `|J| ≤ ℓ_h`, where `ℓ_h ≥ 2` if `J ≠ ∅`, such that
every vertex of `N_G(h) \ J` has level at least 2. Let `ℓ'` lower the levels of the vertices of
`N_G(h) \ J` by one. If `(G − h, ℓ')` is good, then `(G, ℓ)` is good.

**Formalization Note** Levels are natural numbers with `ℓ v ≥ 1` for all `v`; `G − h` is the
induced subgraph on `{v // v ≠ h}`; the lowered level `ℓ v − 1` is applied only to vertices of
level at least 2, so it never truncates. -/
theorem lemma_8_29 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (ℓ : V → ℕ)
    (hℓ : ∀ v, 1 ≤ ℓ v) (h : V) (J : Finset V) (hJ : ∀ v ∈ J, G.Adj h v) (hJcard : J.card ≤ ℓ h)
    (hJh : J.Nonempty → 2 ≤ ℓ h) (hrest : ∀ v, G.Adj h v → v ∉ J → 2 ≤ ℓ v)
    (hgood : IsLevelGood (G.induce {v | v ≠ h})
      (fun v => if G.Adj h v.1 ∧ v.1 ∉ J then ℓ v.1 - 1 else ℓ v.1)) :
    IsLevelGood G ℓ := by sorry

end SparseDisc
