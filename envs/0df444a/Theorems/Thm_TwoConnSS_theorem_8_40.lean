-- Prove2me | Theorems.Thm_TwoConnSS_theorem_8_40
-- name    : TwoConnSS.theorem_8_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:34.982632+00:00
-- url     : https://prove2.me/theorems/becd81e1-9c3d-40b6-a2a5-04d4a785b293
-- title:
--   Theorem 8.40 — no 5-cycle component, and one neighbour per 4-cycle (Algorithm B)
-- statement:
--   Let $G$ be structured with initial cover $S_0$, and let $S$ be a canonical 2-edge-cover for Algorithm B whose 4-cycle components are primitive. In polynomial time one can construct a canonical 2-edge-cover $S'$ for Algorithm B with no 5-cycle component and exactly one neighbouring component for every 4-cycle component, such that $\mathrm{cost}_B(S') \le \mathrm{cost}_B(S)$. $S'$ is reached from $S$ by successful exchanges of Algorithm B, each of which satisfies
--   $$W_B(T') \ge W_B(T),\qquad s_B(T') < s_B(T)$$
--   for its input $T$ and output $T'$. If $S$ already has the two properties, $S' = S$.
--
--   These are the small-cycle eliminations that prepare Algorithm B's bridge covering.
--
--   Differences from the source:
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - reading: the initial cover S₀ and the primitive-4-cycle invariant (p.35: 'Our exchanges maintain that every 4-cycle component is primitive') → an input `S₀` with `IsInitialCover G S₀`, and every 4-cycle component of `S` primitive relative to `S₀`; reason: primitivity and the successful exchanges are defined relative to S₀, so it must be an argument
--   - reading: every completed exchange preserves the blocks in L, surviving primitive 4-cycles and a component with at least ten vertices → each step is a `SuccB` (canonical for B, which includes a component with at least ten vertices; primitive; L-blocks preserved; cost non-increasing) with W_B non-decreasing and s_B decreasing; reason: each completed exchange is a successful exchange in the paper's convention (p.40: 'In every exchange lemma, the term successful includes canonicality, nonincreasing cost, and strict progress of the appropriate potential'; proof of Theorem 8.40, p.66: 'They preserve canonicality and the stated block conditions'), so the per-step canonicity and cost monotonicity are part of the theorem as the paper uses it
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 8.40, p.66 (PDF p.67)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccB

namespace TwoConnSS

/-- **Theorem 8.40: eliminating 5-cycle components and 4-cycles with several neighbours.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 8.40, p.66: "Let S be
canonical for Algorithm B in a structured graph. In polynomial time one can construct a canonical
2-edge-cover S′ with no 5-cycle component and with exactly one neighboring component for every
4-cycle component, such that costB(S′) ≤ costB(S). Every completed exchange preserves the blocks in
L inside blocks of the same class, preserves surviving primitive 4-cycles and a component with at
least ten vertices, and satisfies WB(S′) ≥ WB(S), sB(S′) < sB(S), where S, S′ in this display
denote its input and output. Thus each exchange strictly decreases ϕB. If the input already has the
required properties, the algorithm returns it unchanged."

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` such that for every
structured `G`, initial cover `S₀` and cover `S` canonical for B with every 4-cycle component
primitive, the output `S'` satisfies:
1. `S'` is canonical for B, has no 5-cycle component, and every 4-cycle component of `S'` has
   exactly one neighbouring component;
2. `cost_B(S') ≤ cost_B(S)`;
3. `S'` is reached from `S` by a finite chain of exchanges `T → T'`, each a successful B-exchange
   (canonical, blocks of `L(T)` inside blocks of `L(T')`, 4-cycles primitive, cost non-increasing)
   with `W_B(T') ≥ W_B(T)` and `s_B(T') < s_B(T)`;
4. if `S` already has no 5-cycle component and one neighbouring component per 4-cycle component,
   then `S' = S`.

**Formalization Note.** Primitivity refers to the initial cover `S₀`, an input (the invariant of
p.35). "A component with at least ten vertices" is part of canonicity for B. -/
theorem theorem_8_40 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonB I.graph (toEdges I.n lS) →
        let S := toEdges I.n lS
        let S' := toEdges I.n ((alg (I, [l₀, lS])).getD 0 [])
        IsCanonB I.graph S' ∧ BReady I.graph S' ∧ costB S' ≤ costB S ∧
        Relation.ReflTransGen
          (fun T T' => SuccB I.graph (toEdges I.n l₀) T T' ∧ WB T ≤ WB T' ∧ sB T' < sB T) S S' ∧
        (BReady I.graph S → S' = S) := by sorry

end TwoConnSS
