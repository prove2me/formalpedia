-- Prove2me | Theorems.Thm_TwoConnSS_Supplement_theorem_8_35
-- name    : TwoConnSS.Supplement.theorem_8_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:48:16.56736+00:00
-- url     : https://prove2.me/theorems/ba0a913e-65a0-4840-8de3-e7be5b377af7
-- title:
--   Theorem 8.35 — one exchange removes a 4-cycle component with two distinct neighbours (Algorithm B)
-- statement:
--   Fix parameters $11/9\le\alpha<5/4$ and $0<\eta\le1/100$, and work under the standing assumptions of §8.3 (Algorithm B): $G$ is an $(\alpha,\eta)$-structured graph, $S_0$ is its initial cover, and every 4-cycle component of the current cover is primitive with respect to $S_0$.
--
--   Let $S$ be a canonical 2-edge-cover for Algorithm B with no 5-cycle component, and suppose some 4-cycle component of $S$ has at least two distinct neighbouring components in the component graph $G_S$. Then one can construct, in polynomial time, a 2-edge-cover $S'$ such that:
--
--   1. $S'$ is canonical for Algorithm B;
--   2. every block of $L(S)$ (the 2EC blocks that are not 4- or 5-cycles) lies inside a block of $L(S')$;
--   3. every 4-cycle component of $S'$ is primitive with respect to $S_0$;
--   4. $$\mathrm{cost}_B(S')\le\mathrm{cost}_B(S),\qquad W_B(S')\ge W_B(S),\qquad s_B(S')<s_B(S);$$
--   5. $S'$ has fewer 4-cycle components than $S$ and no 5-cycle component;
--   6. $\phi_B(S')<\phi_B(S)$, where $\phi_B=(-W_B,s_B,\mathrm{br})$ is compared lexicographically.
--
--   Here $s_B$ counts all 4-cycle and 5-cycle blocks, including those inside complex components, whereas clause 5 counts components. No bridgelessness of $S'$ is claimed: the exchange may create bridges.
--
--   This is the single exchange that Algorithm B repeats to remove branching 4-cycle components before bridge covering.
--
--   **Formalization Note** The standing hypotheses are those of the base milestone `TwoConnSS.theorem_8_40`, and all objects ($\mathrm{cost}_B$, $L$, $W_B$, $s_B$, $\phi_B$, canonicity, primitivity) are the base mission's published definitions. The machine (`Turing.TM2ComputableInPolyTime` on `encInL`/`encLists`) reads $(G,[S_0,S])$ and returns $S'$ as its first list; it is fixed before the instance.
--
--   Differences from the source:
--   - reading: "preserves the primitivity of every surviving 4-cycle" → every 4-cycle component of $S'$ is primitive with respect to $S_0$; reason: the proof (p.60) shows that no new 4-cycle block is created, so every 4-cycle component of $S'$ is a surviving one; this reading is the stronger one and matches the published successful-exchange condition `SuccB`.
--   - encoding: the standing assumptions of §8.3 (structured graph, initial cover $S_0$, primitive 4-cycle components) → explicit hypotheses with $11/9\le\alpha<5/4$, $0<\eta\le1/100$; reason: the same binders as the published Theorem 8.40.
--   - encoding: polynomial time → `Turing.TM2ComputableInPolyTime` on `encInL`/`encLists`; reason: Lean convention shared with the base milestones.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), Theorem 8.35, p.59 (PDF 60), §8.3.1; proof pp.59–60 (PDF 60–61)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccB

namespace TwoConnSS.Supplement

open TwoConnSS Classical

/-- **Theorem 8.35: one exchange removes a 4-cycle component with two distinct neighbours.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 8.35, p.59 (§8.3.1,
Algorithm B); proof pp.59–60: "Let S be a canonical 2-edge-cover for Algorithm B with no 5-cycle
component. Suppose that a 4-cycle component has at least two distinct neighbors in GS. In
polynomial time, one can construct a canonical 2-edge-cover S′ for Algorithm B that preserves the
blocks in L(S) inside blocks of L(S′), preserves the primitivity of every surviving 4-cycle, and
satisfies costB(S′) ≤ costB(S), WB(S′) ≥ WB(S), sB(S′) < sB(S). Moreover, S′ has fewer 4-cycle
components and no 5-cycle component. … Thus ϕB(S′) < ϕB(S), even if the exchange creates bridges."

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` such that for every
structured `G`, initial cover `S₀` and cover `S` canonical for B, with every 4-cycle component
primitive, no 5-cycle component, and some 4-cycle component with at least two neighbouring
components, the output `S'` satisfies:
1. `S'` is canonical for B;
2. every block of `L(S)` lies inside a block of `L(S')`;
3. every 4-cycle component of `S'` is primitive (w.r.t. `S₀`);
4. `cost_B(S') ≤ cost_B(S)`, `W_B(S') ≥ W_B(S)`, `s_B(S') < s_B(S)`;
5. `S'` has fewer 4-cycle components than `S`, and no 5-cycle component;
6. `ϕ_B(S') < ϕ_B(S)` (lexicographic `(−W_B, s_B, br)`).

**Formalization Note.** The standing hypotheses of §8.3 (structured graph, initial cover `S₀` an
input, primitive 4-cycle components — the invariant of p.35 and p.55) are the binders of the
published `TwoConnSS.theorem_8_40`. "Neighbours in `G_S`" are the components of `S` other than
the 4-cycle joined to it by an edge of `G` (`nbrComps`). `s_B` counts 4- and 5-cycle blocks,
including those in complex components; the "fewer 4-cycle components" clause counts components.
No bridgelessness of `S'` is claimed. Clause 3 is stated for every 4-cycle component of `S'`; the
proof shows that no new 4-cycle block is created, so every 4-cycle component of `S'` is a surviving
one. The machine reads `(G, [S₀, S])` and returns `S'` as the first list. -/
theorem theorem_8_35 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonB I.graph (toEdges I.n lS) →
        (∀ C, ¬ IsCycleComp (toEdges I.n lS) C 5) →
        (∃ C, IsCycleComp (toEdges I.n lS) C 4 ∧
          2 ≤ (nbrComps I.graph (toEdges I.n lS) C).card) →
        let S := toEdges I.n lS
        let S' := toEdges I.n ((alg (I, [l₀, lS])).getD 0 [])
        IsCanonB I.graph S' ∧ (∀ B ∈ Lbl S, ∃ B' ∈ Lbl S', B ⊆ B') ∧
        Primitive (toEdges I.n l₀) S' ∧
        costB S' ≤ costB S ∧ WB S ≤ WB S' ∧ sB S' < sB S ∧
        ((comps S').filter fun C => IsCycleComp S' C 4).card <
          ((comps S).filter fun C => IsCycleComp S C 4).card ∧
        (∀ C, ¬ IsCycleComp S' C 5) ∧ LexB S S' := by sorry

end TwoConnSS.Supplement
