-- Prove2me | Theorems.Thm_TwoConnSS_theorem_8_41
-- name    : TwoConnSS.theorem_8_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:49:02.985405+00:00
-- url     : https://prove2.me/theorems/0c36910b-87d6-4f3a-9e15-95c2922281dd
-- title:
--   Theorem 8.41 — bridge covering under assignment B
-- statement:
--   Let $G$ be structured with initial cover $S_0$. Suppose $S$ satisfies the augmentation invariant of Algorithm B (canonical for B, 4-cycle components primitive), contains a bridge, has no 5-cycle component, and every 4-cycle component is adjacent to exactly one other component. In polynomial time one can construct a canonical 2-edge-cover $S'$ for Algorithm B, with primitive 4-cycle components, every block of $L(S)$ inside a block of $L(S')$, $\mathrm{cost}_B(S') \le \mathrm{cost}_B(S)$, and one of:
--
--   1. $W_B(S') > W_B(S)$;
--   2. $W_B(S') = W_B(S)$ and $s_B(S') < s_B(S)$;
--   3. $W_B(S') = W_B(S)$, $s_B(S') = s_B(S)$ and $\mathrm{br}(S') < \mathrm{br}(S)$.
--
--   Repeating it removes all bridges of Algorithm B's cover.
--
--   Differences from the source:
--   - reading: the augmentation invariant of Algorithm B → canonical for B (with a component on at least ten vertices) and every 4-cycle component primitive relative to the input S₀ with `IsInitialCover G S₀`; reason: p.56: 'Algorithm B maintains a canonical 2-edge-cover … Its successful exchanges maintain primitive 4-cycle components'
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 8.41, p.67 (PDF p.68)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccB

namespace TwoConnSS

/-- **Theorem 8.41: bridge covering under assignment B.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 8.41, p.67: "Suppose S
satisfies the augmentation invariant of Algorithm B, contains a bridge, has no 5-cycle component, and
every 4-cycle component is adjacent to exactly one other component. In polynomial time, one can
construct a canonical 2-edge-cover S′ that preserves the augmentation invariant, including the old
blocks in L, the surviving primitive 4-cycles, and a component with at least ten vertices, such that
costB(S′) ≤ costB(S), ϕB(S′) < ϕB(S). More precisely, one of the following holds: 1. WB(S′) >
WB(S); 2. WB(S′) = WB(S) and sB(S′) < sB(S); 3. WB(S′) = WB(S), sB(S′) = sB(S), and br(S′) <
br(S)."

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` such that for every
structured `G`, initial cover `S₀` and cover `S` that is canonical for B with every 4-cycle
component primitive, has a bridge, has no 5-cycle component and has exactly one neighbouring
component per 4-cycle component, the output `S'` is a successful B-exchange of `S`: canonical for B
(with a component on at least ten vertices), every 4-cycle component primitive, every block of
`L(S)` inside a block of `L(S')`, `cost_B(S') ≤ cost_B(S)`, and one of the three alternatives.

**Formalization Note.** "The augmentation invariant of Algorithm B" is read as canonicity for B
together with primitive 4-cycles (p.56: "Algorithm B maintains a canonical 2-edge-cover as in
Definition 8.7, including the existence of a component with at least ten vertices. Its successful
exchanges maintain primitive 4-cycle components and preserve every block that is neither a 4-cycle
nor a 5-cycle inside a block of the same class"). `G` structured is the standing assumption of §8;
primitivity refers to the initial cover `S₀`, an input. -/
theorem theorem_8_41 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonB I.graph (toEdges I.n lS) → 0 < br (toEdges I.n lS) →
        BReady I.graph (toEdges I.n lS) →
        SuccB I.graph (toEdges I.n l₀) (toEdges I.n lS)
          (toEdges I.n ((alg (I, [l₀, lS])).getD 0 [])) := by sorry

end TwoConnSS
