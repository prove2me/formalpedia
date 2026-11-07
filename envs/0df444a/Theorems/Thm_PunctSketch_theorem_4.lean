-- Prove2me | Theorems.Thm_PunctSketch_theorem_4
-- name    : PunctSketch.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:04.378421+00:00
-- url     : https://prove2.me/theorems/17f1b1b0-8b5d-4d71-a7ea-5d794b19cf60
-- title:
--   Theorem 4, p.10 — a deterministic puncturable sketch of $O((d+k)\log n)$ bits
-- statement:
--   There is a constant $A>0$ such that for all $n,d,k$ there are a prime $Q$, a number of rows $D\le 2d+k$ with
--   $$D\,\lceil\log_2Q\rceil\le A\,(d+k)\log_2n,$$
--   a matrix $\Psi\in\mathbb F_Q^{D\times n}$ and a decoder, all fixed before the graph, with this property: for every graph $G$ on $n$ vertices and every $F$ with $|F|<k$, the map $C\mapsto$ decoder$(F,C,(\Psi\boldsymbol a^\pm_v)_v)$ is a boundary retrieval oracle for $G\setminus F$ with capacity $d$.
--
--   Each node knows only its neighbourhood, and its message $\Psi\boldsymbol a^\pm_v$ is linear in its signed adjacency vector and uses no randomness. The set $F$ is chosen after the messages are sent.
--
--   Differences from the source:
--   - generalization: d + k < n → no relation between d + k and n; reason: the condition reflects the use (footnote 7, p.15) and is not used by the argument; the theorem specializes to it
--   - encoding: O((d + k) log n) bits → D⌈log₂ Q⌉ ≤ A (d + k) log₂ n, with A before n, d, k; reason: the bit count of D elements of 𝔽_Q; the universal constant is explicit
--   - encoding: a boundary retrieval oracle for G ⧵ F, with queries C ⊆ V ⧵ F and boundary in G ⧵ F → queries C disjoint from F, boundary ∂_{−F}C; reason: this is eq. (1): the boundary of C in G ⧵ F
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 4, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_PunctSketch_IsPuncturableRetrieval

namespace PunctSketch

/-- **Theorem 4 (puncturable sparse recovery).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Theorem 4, p.10. Each node can produce a
deterministic linear sketch using `O((d + k) log n)` bits such that for every `F` with `|F| < k` the
receiver can implement a boundary retrieval oracle for `G ∖ F` with capacity `d`.

There is a constant `C` such that for all `n, d, k` there are a prime `Q`, a matrix `Ψ` with `D ≤ 2d + k`
rows over `𝔽_Q` and a decoder, all chosen before the graph, with `D ⌈log₂ Q⌉ ≤ C (d + k) log₂ n`, and
the decoder applied to `F`, `C` and the sketches `Ψ𝒂±_v` returns `∂_{−F} C` when its size is at most `d`.

**Formalization Note.** The page's `d + k < n` is dropped: it reflects the use (footnote 7, p.15), and
the statement specializes to it. -/
theorem theorem_4 :
    ∃ A : ℝ, 0 < A ∧ ∀ n d k : ℕ, ∃ (Q D : ℕ), Q.Prime ∧ D ≤ 2 * d + k ∧
      ((D : ℝ) * (Nat.clog 2 Q : ℝ) ≤ A * ((d : ℝ) + k) * Real.logb 2 n) ∧
      ∃ (Ψ : Matrix (Fin D) (Fin n) (ZMod Q))
        (dec : Finset (Fin n) → Finset (Fin n) → (Fin n → Fin D → ZMod Q) → Finset (Sym2 (Fin n))),
        IsPuncturableRetrieval k d Ψ dec := by sorry

end PunctSketch
