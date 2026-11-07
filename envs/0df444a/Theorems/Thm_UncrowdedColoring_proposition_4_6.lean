-- Prove2me | Theorems.Thm_UncrowdedColoring_proposition_4_6
-- name    : UncrowdedColoring.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:50.095764+00:00
-- url     : https://prove2.me/theorems/366c85e9-0414-4d5b-821b-11a32133474a
-- title:
--   Proposition 4.6 (corrected: $|L_1(v)|=\lceil q_1\rceil$) — $(L_1,F_1)$ satisfies $P(1)$
-- statement:
--   Let $H$ be a $k$-uniform uncrowded hypergraph on a finite vertex set and $L$ a list assignment satisfying (C1) and (C2) of Theorem 1.8. Obtain $L_1$ by removing colors from each $L(v)$ arbitrarily down to size $\lceil q_1\rceil$, and let $F_{1,c}$ have edge set $\{e\in E(H):c\in\bigcap_{v\in e}L_1(v)\}$. Then $F_1$ is a family of restriction hypergraphs with respect to $L_1$ and
--   $$(L_1,F_1)\text{ satisfies }P(1).$$
--
--   This is the start of the iteration.
--
--   Differences from the source:
--   - correction: (Q2) of Definition 4.5 prints |L(v)| = q_i with q_i real → |L(v)| = ⌈q_i⌉ in SatisfiesP; reason: the printed condition is false for nonempty instances: k = 2, ε = 1/2, integer d ≥ 2 give q_1 = (3/2)d/log d, irrational since log d is transcendental, so no finite list has size q_1; p.14 warns that ceilings are omitted
--   - generalization: d ≥ d_0 with d_0 ∈ ℕ, d read as an integer → d : ℝ with (d₀ : ℝ) ≤ d; reason: §7, eq. (81), p.53 applies the results at a non-integer d; natural d is a cast
--   - encoding: remove max{|L(v)| − q_1, 0} colors arbitrarily → every L₁ with L₁ v ⊆ L v and |L₁ v| = ⌈q_1⌉; L may be infinite; reason: (C1) gives |L(v)| ≥ ⌈q_1⌉, so the trimmed size is ⌈q_1⌉
--   - encoding: a finite vertex set → V : Type with H.vertexSet.Finite; reason: every finite hypergraph is isomorphic to one on a type in Type
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Proposition 4.6, p.18

import Mathlib
import Definitions.Def_UncrowdedColoring_IsUncrowded
import Definitions.Def_UncrowdedColoring_IsUniform
import Definitions.Def_UncrowdedColoring_SatisfiesP
import Definitions.Def_UncrowdedColoring_fOne

open scoped Classical

namespace UncrowdedColoring

/-- **Proposition 4.6**, p.18: `(L_1, F_1)` satisfies `P(1)`, with `|L_1(v)| = ⌈q_1⌉`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Proposition 4.6, p.18.

**Formalization Note.** `L_1` is any trimming of `L` to size `⌈q_1⌉` ("removing colors arbitrarily");
lists may be infinite, and (C1) forces `|L(v)| ≥ ⌈q_1⌉`. The statement includes "F_1 is a family of
restriction hypergraphs" from the paragraph above the proposition. `d₀` only ensures `1 ∈ [s]`. -/
theorem proposition_4_6 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ d₀ : ℕ, ∀ d : ℝ, (d₀ : ℝ) ≤ d →
      ∀ (V : Type) (H : Hypergraph V) (U : Finset V), (U : Set V) = H.vertexSet →
        IsUniform H k → IsUncrowded H →
        ∀ L : V → Set ℕ,
          -- (C1)
          (∀ v ∈ H.vertexSet, (L v).Infinite ∨
            (1 + ε) * (((k : ℝ) - 1) * (d / Real.log d)) ^ (1 / ((k : ℝ) - 1)) ≤ ((L v).ncard : ℝ)) →
          -- (C2)
          (∀ v ∈ H.vertexSet, ∀ c ∈ L v,
            (({e | e ∈ H.edgeSet ∧ v ∈ e ∧ ∀ u ∈ e, c ∈ L u} : Set (Set V)).ncard : ℝ) ≤ d) →
          ∀ L₁ : V → Finset ℕ,
            (∀ v ∈ U, (L₁ v : Set ℕ) ⊆ L v ∧ (L₁ v).card = ⌈qSeq k ε d 1⌉₊) →
            IsRestrictionFamily U L₁ (fOne H U L₁) ∧
              SatisfiesP k ε d 1 U L₁ (fOne H U L₁) := by sorry

end UncrowdedColoring
