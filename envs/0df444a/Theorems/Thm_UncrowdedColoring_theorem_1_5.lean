-- Prove2me | Theorems.Thm_UncrowdedColoring_theorem_1_5
-- name    : UncrowdedColoring.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:20.395206+00:00
-- url     : https://prove2.me/theorems/c185eef0-b463-4085-b855-8b3258cb589b
-- title:
--   Theorem 1.5 — the list chromatic number of uncrowded hypergraphs at the shattering threshold
-- statement:
--   Let $k\ge 2$ be an integer and $\varepsilon>0$. There is $\Delta_0\in\mathbb N$ such that every $k$-uniform uncrowded hypergraph $H$ of maximum degree at most $\Delta\ge\Delta_0$ satisfies
--   $$\chi_\ell(H)\le(1+\varepsilon)\Big((k-1)\frac{\Delta}{\log\Delta}\Big)^{\frac{1}{k-1}}.$$
--
--   This determines the leading constant up to the shattering threshold: the constant $(k-1)^{1/(k-1)}$ improves the earlier $k-1$, and for $k=2$ the statement recovers Kim's bound for graphs of girth $5$.
--
--   **Formalization Note** $\Delta_0$ depends only on $k,\varepsilon$ and is quantified before the hypergraph. `listChromaticNumber` is the minimum of a nonempty set (see the sanity file), and `Real.log` is the natural logarithm, as on p.12.
--
--   Differences from the source:
--   - generalization: ∆ ≥ ∆_0 with ∆_0 ∈ ℕ, ∆ read as an integer → Δ : ℝ with (Δ₀ : ℝ) ≤ Δ and degrees bounded by the real Δ; reason: a natural ∆ is a cast, and the real case covers the integer case
--   - encoding: a finite vertex set → V : Type with H.vertexSet.Finite; reason: every finite hypergraph is isomorphic to one on a type in Type
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 1.5, p.4

import Mathlib
import Definitions.Def_UncrowdedColoring_IsUncrowded
import Definitions.Def_UncrowdedColoring_IsUniform
import Definitions.Def_UncrowdedColoring_degree
import Definitions.Def_UncrowdedColoring_listChromaticNumber

namespace UncrowdedColoring

/-- **Theorem 1.5**, p.4: every `k`-uniform uncrowded hypergraph of maximum degree at most
`Δ ≥ Δ₀` satisfies `χ_ℓ(H) ≤ (1 + ε)((k − 1) Δ / log Δ)^{1/(k−1)}`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 1.5, p.4.

**Formalization Note.** `k = 2` and large `ε` are included. `Δ₀` depends only on `k`, `ε` and precedes
the hypergraph. `Δ` is real; a natural `Δ` is a cast. The exponent covers the whole bracket, including
`k − 1` (rendered p.4). The vertex type lives in `Type`, which loses nothing, as every finite hypergraph
is isomorphic to one on `Type`. `Real.log` is the paper's `log` (p.12 reads it as the natural
logarithm). `Δ₀` keeps `Real.log Δ > 0`. -/
theorem theorem_1_5 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ₀ : ℕ, ∀ (V : Type) (H : Hypergraph V) (Δ : ℝ), H.vertexSet.Finite → (Δ₀ : ℝ) ≤ Δ →
      IsUniform H k → IsUncrowded H → (∀ v ∈ H.vertexSet, (degree H v : ℝ) ≤ Δ) →
      (listChromaticNumber H : ℝ) ≤
        (1 + ε) * (((k : ℝ) - 1) * (Δ / Real.log Δ)) ^ (1 / ((k : ℝ) - 1)) := by sorry

end UncrowdedColoring
