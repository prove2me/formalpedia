-- Prove2me | Theorems.Thm_SteinerNav_theorem_3
-- name    : SteinerNav.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:11.993719+00:00
-- url     : https://prove2.me/theorems/7592d79a-61e3-43b4-832a-774adc5c6bc3
-- title:
--   Theorem 3 (existence part) — a Steiner $(1+1/d)$-navigable graph with $|R|=O(\sqrt{nL\log n})$ and $|E|=O(\min\{n^2,n^{3/2}\sqrt{L\log n}\})$
-- statement:
--   There are absolute constants $C_1,C_2>0$ with the following property. Let $d\ge1$, let $P\subset\mathbb R^d$ be a set of $n\ge2$ distinct points with aspect ratio $\Delta$, and set $\alpha=1+1/d$ and $L=1+\lfloor\log_2\Delta\rfloor$. There is a Steiner $\alpha$-navigable graph $G$ on $P\cup R$, with no Steiner-to-Steiner edges and no self-loops, such that
--   $$|R|\le n,\qquad |R|\le C_1\sqrt{nL\ln n},\qquad |E(G)|\le C_2\min\{n^2,\ n^{3/2}\sqrt{L\ln n}\}.$$
--
--   This is the construction behind Theorem 1. The paper's Theorem 3 ends with a further sentence on the running time of the construction ("Such a graph can be constructed in $\tilde O(n^2d)$ time with high probability"); that sentence is a statement about an algorithm and is not part of this item, whose title marks it as the existence part.
--
--   **Formalization Note** The $O(\cdot)$ bounds are absolute constants chosen before $d$, $n$ and $P$. Logarithms are natural; another fixed base changes only the constants.
--
--   Differences from the source:
--   - generalization: "with no Steiner-to-Steiner edges" → also no self-loops; reason: the construction "always exclud[es] self-loops" (p.8), and dropping the clause gives the page's statement.
--   - encoding: O(·) → absolute constants C₁, C₂ before d, n and P; natural logarithm; reason: the meaning of O(·) here (the page's constants depend on nothing), and a change of log base changes only the constants.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 3, p.8 (existence part; self-loops excluded, p.8)

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio

namespace SteinerNav

/-- Theorem 3, existence clause: absolute constants `C₁, C₂` such that for every `d ≥ 1` and every `P` with
`n = |P| ≥ 2`, for `α = 1 + 1/d` and `L = 1 + ⌊log₂ Δ⌋`, there is a Steiner `α`-navigable graph on `P ∪ R`,
with no self-loops and no Steiner-to-Steiner edges, with `|R| ≤ n`, `|R| = O(√(nL log n))` and
`|E(G)| = O(min{n², n^{3/2} √(L log n)})` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 3, p.8; self-loops excluded, p.8).

**Formalization Note** The constants come before `d` and `P`. Logarithms are natural. The sentence of
Theorem 3 on the running time is not part of this item. -/
theorem theorem_3 : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (d : ℕ), 1 ≤ d →
    ∀ P : Finset (Pt d), 2 ≤ P.card →
      let n : ℝ := (P.card : ℝ)
      let L : ℝ := (annulusCount P : ℝ)
      ∃ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
        IsSteinerNavigable (1 + 1 / (d : ℝ)) P R E ∧
        NoSteinerToSteiner R P E ∧
        (∀ x, (x, x) ∉ E) ∧
        R.card ≤ P.card ∧
        (R.card : ℝ) ≤ C₁ * Real.sqrt (n * L * Real.log n) ∧
        (E.card : ℝ) ≤ C₂ * min (n ^ 2) (n ^ (3 / 2 : ℝ) * Real.sqrt (L * Real.log n)) := by sorry

end SteinerNav
