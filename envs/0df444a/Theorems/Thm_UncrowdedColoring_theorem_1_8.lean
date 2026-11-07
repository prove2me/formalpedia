-- Prove2me | Theorems.Thm_UncrowdedColoring_theorem_1_8
-- name    : UncrowdedColoring.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:07.966525+00:00
-- url     : https://prove2.me/theorems/254dc05a-0eed-47f9-96e0-f4d5f73a3be4
-- title:
--   Theorem 1.8 — list coloring in the color-degree setting
-- statement:
--   Let $k\ge 2$ be an integer and $\varepsilon>0$. There is $d_0\in\mathbb N$ such that for every $d\ge d_0$ the following holds. Let $H$ be a $k$-uniform uncrowded hypergraph and $L:V(H)\to 2^{\mathbb N}$ a list assignment with
--
--   1. (C1) $|L(v)|\ge(1+\varepsilon)\big((k-1)\tfrac{d}{\log d}\big)^{1/(k-1)}$ for every $v$;
--   2. (C2) $\big|\{e\in E(H,v):c\in\bigcap_{u\in e}L(u)\}\big|\le d$ for every $v$ and $c\in L(v)$.
--
--   Then $H$ admits an $L$-coloring.
--
--   This is the paper's main technical result, replacing the degree by the color degree; the goal theorem follows from it.
--
--   **Formalization Note** Infinite lists are allowed; (C1) reads `(L v).Infinite ∨ …` since `ncard` is $0$ on an infinite set.
--
--   Differences from the source:
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the theorem at a non-integer d; natural d is a cast
--   - encoding: a finite vertex set → V : Type with H.vertexSet.Finite; reason: every finite hypergraph is isomorphic to one on a type in Type
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 1.8, p.6

import Mathlib
import Definitions.Def_UncrowdedColoring_IsUncrowded
import Definitions.Def_UncrowdedColoring_IsUniform
import Definitions.Def_UncrowdedColoring_listChromaticNumber

namespace UncrowdedColoring

/-- **Theorem 1.8**, p.6: the color-degree theorem.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 1.8, p.6.

**Formalization Note.** `d` is real: §7, eq. (81), p.53 applies the theorem at a non-integer `d`.
Lists are arbitrary subsets of `ℕ`, possibly infinite; `(L v).Infinite ∨ …` is (C1), since `ncard` of an
infinite set is `0`. The vertex type lives in `Type`, which loses nothing, as every finite hypergraph
is isomorphic to one on `Type`. `Real.log` is the paper's `log` (p.12 reads it as the natural
logarithm). All `ε > 0` are allowed; `ε < 1` is only assumed in §§4–5. -/
theorem theorem_1_8 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (H : Hypergraph V), H.vertexSet.Finite →
        IsUniform H k → IsUncrowded H →
        ∀ L : V → Set ℕ,
          -- (C1)
          (∀ v ∈ H.vertexSet, (L v).Infinite ∨
            (1 + ε) * (((k : ℝ) - 1) * (d / Real.log d)) ^ (1 / ((k : ℝ) - 1)) ≤ ((L v).ncard : ℝ)) →
          -- (C2)
          (∀ v ∈ H.vertexSet, ∀ c ∈ L v,
            (({e | e ∈ H.edgeSet ∧ v ∈ e ∧ ∀ u ∈ e, c ∈ L u} : Set (Set V)).ncard : ℝ) ≤ d) →
          ∃ Φ : V → ℕ, IsListColoring H L Φ := by sorry

end UncrowdedColoring
