-- Prove2me | Theorems.Thm_UncrowdedColoring_Supplement_theorem_7_1
-- name    : UncrowdedColoring.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:05:44.957365+00:00
-- url     : https://prove2.me/theorems/36e3d610-ceb3-4ea4-976c-e4bcfdfd1ff7
-- title:
--   Theorem 7.1 — palette sparsification for uncrowded hypergraphs
-- statement:
--   Let $k \ge 2$ be an integer and $\varepsilon > 0$. There is a constant $C > 0$ (depending only on $k$ and $\varepsilon$) such that for every $\gamma \in (0,1)$ there is $\Delta_0 \in \mathbb N$ (depending on $k$, $\varepsilon$, $\gamma$) with the following property. Let $\Delta \ge \Delta_0$, $n \in \mathbb N$, and let $q, q' \in \mathbb N$ with $q' \le q$ satisfy
--
--   $$
--   q \ge (1+\varepsilon)\left(\frac{k-1}{\gamma}\cdot\frac{\Delta}{\log \Delta}\right)^{\frac{1}{k-1}}
--   \qquad\text{and}\qquad
--   q' \ge \Delta^{\frac{\gamma}{k-1}} + C(\log n)^{\frac1k}.
--   $$
--
--   Let $H$ be a $k$-uniform uncrowded hypergraph on $n$ vertices in which every vertex has degree at most $\Delta$. For each vertex $v \in V(H)$, independently sample a subset $L(v) \subseteq [q] = \{1,\dots,q\}$ of size $q'$ uniformly at random. Then
--
--   $$
--   \Pr_L\big[\,H \text{ admits an } L\text{-coloring}\,\big] \;\ge\; 1 - \frac1n .
--   $$
--
--   Here an $L$-coloring assigns to every vertex $v$ a color in $L(v)$ so that no edge is monochromatic, and $\log$ is the natural logarithm.
--
--   This is a palette sparsification theorem: although $H$ may need about $((k-1)\Delta/\log\Delta)^{1/(k-1)}$ colors, sampling only about $\Delta^{\gamma/(k-1)}$ of them per vertex, from a palette larger by the factor $\gamma^{-1/(k-1)}$, already suffices with high probability. In the paper it is derived from the color-degree theorem (Theorem 1.8).
--
--   **Formalization Note** Quantifiers are in the paper's order: $C$ is chosen before $\gamma$, and $\Delta_0$ before $\Delta, n, q, q', H$. The probability is the counting ratio of the definition `sampledListProb`. The vertex type lives in Lean's `Type`, as in the published Theorem 1.5.
--
--   Differences from the source:
--   - generalization: Δ ≥ Δ₀ with Δ the integer maximum-degree bound → Δ any real number with Δ ≥ Δ₀; reason: an integer Δ is a special case (its cast), so the Lean statement specializes to the source's; same convention as the published Theorem 1.5
--   - encoding: independently sample a uniform q′-subset L(v) ⊆ [q] for each vertex → the counting ratio over all assignments V(H) → ([q] choose q′) (definition sampledListProb); reason: the product of independent uniform laws on a finite set is the uniform law on the product, so the probabilities are equal
--   - encoding: an n-vertex hypergraph → a hypergraph on a vertex type in Type with V(H) finite and V(H).ncard = n; lists are extended by ∅ outside V(H); reason: Lean convention of the published mission; same instances
--   - encoding: log n and 1/n at n = 0 (undefined in the source) → Real.log 0 = 0 and 1/0 = 0, so the conclusion reads probability ≥ 1, which the empty hypergraph meets; reason: Lean's total functions; only the degenerate n = 0 case is affected and there the statement is true
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Theorem 7.1, p.53 (PDF p.54)

import Mathlib
import Definitions.Def_UncrowdedColoring_IsUncrowded
import Definitions.Def_UncrowdedColoring_IsUniform
import Definitions.Def_UncrowdedColoring_degree
import Definitions.Def_UncrowdedColoring_listChromaticNumber
import Definitions.Def_UncrowdedColoring_Supplement_sampledListProb

namespace UncrowdedColoring

namespace Supplement

/-- **Theorem 7.1** (palette sparsification for uncrowded hypergraphs), p.53: for every integer
`k ≥ 2` and `ε > 0` there is `C > 0` such that for every `γ ∈ (0, 1)` there is `Δ₀ ∈ ℕ` with the
following property. If `Δ ≥ Δ₀`, `n ∈ ℕ`, `q′ ≤ q`,
`q ≥ (1 + ε)((k − 1)/γ · Δ/log Δ)^{1/(k−1)}` and `q′ ≥ Δ^{γ/(k−1)} + C (log n)^{1/k}`, and `H` is an
`n`-vertex `k`-uniform uncrowded hypergraph of maximum degree at most `Δ`, then, when each vertex
independently samples a uniformly random `q′`-subset `L(v)` of `[q]`, `H` admits an `L`-coloring with
probability at least `1 − 1/n`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Theorem 7.1, p.53 (PDF p.54).

**Formalization Note.** Quantifier order is the paper's: `C` depends on `k, ε` only, `Δ₀` on
`k, ε, γ`, and both precede `Δ, n, q, q′, H`. `Δ` is real (a natural `Δ` is a cast), as in the
published Theorem 1.5. The exponent `1/(k−1)` covers the whole bracket including `(k−1)/γ`
(rendered p.53). `Real.log` is the paper's natural logarithm; at `n = 0` Lean reads `log 0 = 0` and
`1/0 = 0`, so the bound is `1`, which the empty hypergraph meets. `n`-vertex is
`V(H).ncard = n` with `V(H)` finite. `ε < 1` is not assumed (the proof's WLOG). The vertex type lives
in `Type`, as in the published Theorem 1.5. -/
theorem theorem_7_1 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ Δ₀ : ℕ,
      ∀ (Δ : ℝ) (n q q' : ℕ) (V : Type) (H : Hypergraph V),
        (Δ₀ : ℝ) ≤ Δ → q' ≤ q →
        (1 + ε) * ((((k : ℝ) - 1) / γ) * (Δ / Real.log Δ)) ^ (1 / ((k : ℝ) - 1)) ≤ (q : ℝ) →
        Δ ^ (γ / ((k : ℝ) - 1)) + C * (Real.log n) ^ (1 / (k : ℝ)) ≤ (q' : ℝ) →
        H.vertexSet.Finite → H.vertexSet.ncard = n →
        IsUniform H k → IsUncrowded H → (∀ v ∈ H.vertexSet, (degree H v : ℝ) ≤ Δ) →
        1 - 1 / (n : ℝ) ≤ sampledListProb H q q' (fun L => ∃ Φ, IsListColoring H L Φ) := by sorry

end Supplement

end UncrowdedColoring
