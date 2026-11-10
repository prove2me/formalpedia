-- Prove2me | Theorems.Thm_TwoConnSS_theorem_8_22
-- name    : TwoConnSS.theorem_8_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:49:33.073071+00:00
-- url     : https://prove2.me/theorems/58ad9a68-82b6-419d-a5ca-ca2bb8e61958
-- title:
--   Theorem 8.22 — bridge covering under assignments A and B
-- statement:
--   Let $G$ satisfy the bridge-covering assumptions of §8.1.3 and let $S_0$ be an initial cover of $G$.
--
--   1. **(Algorithm A.)** In polynomial time, from any canonical weak 2-edge-cover $(S, M)$ for Algorithm A whose 4-cycle components are primitive, a finite sequence of successful exchanges of Algorithm A produces $(S', M')$ with $S'$ bridgeless, $(S', M')$ canonical for A, $\mathrm{cost}_A(S') \le \mathrm{cost}_A(S)$, and $\phi_A(S') < \phi_A(S)$ if $S$ has a bridge.
--   2. **(Algorithm B.)** In polynomial time, from any canonical 2-edge-cover $S$ for Algorithm B whose 4-cycle components are primitive, with no 5-cycle component and exactly one neighbouring component per 4-cycle component, a finite sequence of successful exchanges of Algorithm B produces a bridgeless canonical $S'$ for Algorithm B with no 5-cycle component, exactly one neighbouring component per 4-cycle component, $\mathrm{cost}_B(S') \le \mathrm{cost}_B(S)$, and $\phi_B(S') < \phi_B(S)$ if $S$ has a bridge.
--
--   Each exchange of the sequence increases $W_r$ or keeps it and decreases the next coordinate of $\phi_r$. This is the paper's main bridge-covering result: it removes all bridges within the credit budgets.
--
--   Differences from the source:
--   - reading: the 11/10-contractible subgraphs specified below have been excluded (p.41) → every 11/10-contractible subgraph has more than ten vertices (`BridgeCoverAssumptions`); reason: the only such subgraph specified is the ten-vertex subgraph J of p.50; the other assumptions of p.41 are stated literally
--   - reading: the initial cover S₀ and the primitive-4-cycle invariant (p.35: 'Our exchanges maintain that every 4-cycle component is primitive') → an input `S₀` with `IsInitialCover G S₀`, and every 4-cycle component of `S` primitive relative to `S₀`; reason: primitivity and the successful exchanges are defined relative to S₀, so it must be an argument
--   - encoding: a sequence of successful exchanges → `Relation.ReflTransGen` of `SuccA`/`SuccB` from the input to the output, each step carrying the per-exchange progress alternatives; reason: a finite chain of exchanges
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 8.22, p.47 (PDF p.48); assumptions §8.1.3, p.41

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_BridgeCoverAssumptions
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccA
import Definitions.Def_TwoConnSS_SuccB

namespace TwoConnSS

/-- **Theorem 8.22: bridge covering under assignments A and B.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 8.22, p.47: "Let S be
canonical for Algorithm r ∈ {A, B} and satisfy the bridge-covering assumptions stated at the start of
Section 8.1.3. In polynomial time, a sequence of successful exchanges produces a bridgeless canonical
cover S′ with costr(S′) ≤ costr(S). If S has a bridge, then ϕr(S′) < ϕr(S). For Algorithm A the
output is a canonical weak 2-edge-cover and may contain unpaired singletons and pairs of singletons.
For Algorithm B it is a canonical 2-edge-cover with no 5-cycle component, and every 4-cycle component
has exactly one neighboring component. For each complete exchange, Algorithm A either increases WA
or leaves WA unchanged and decreases br. Algorithm B either increases WB, or leaves WB unchanged and
decreases sB, or leaves both unchanged and decreases br."

Let `G` satisfy the bridge-covering assumptions of §8.1.3 and let `S₀` be an initial cover of `G`.
1. (r = A) A polynomial-time `alg` maps every `(G, S₀, S, M)` with `(S, M)` canonical for A and every
   4-cycle component of `S` primitive to `(S', M')` reached from `(S, M)` by a finite chain of
   successful A-exchanges, with `S'` bridgeless, `(S', M')` canonical for A,
   `cost_A(S', M') ≤ cost_A(S, M)`, and `ϕ_A(S') < ϕ_A(S)` if `S` has a bridge.
2. (r = B) A polynomial-time `alg` maps every `(G, S₀, S)` with `S` canonical for B, every 4-cycle
   component primitive, no 5-cycle component and every 4-cycle component with exactly one
   neighbouring component, to `S'` reached from `S` by a finite chain of successful B-exchanges,
   with `S'` bridgeless and canonical for B, no 5-cycle component, every 4-cycle component with
   exactly one neighbouring component, `cost_B(S') ≤ cost_B(S)`, and `ϕ_B(S') < ϕ_B(S)` if `S` has
   a bridge.

**Formalization Note.** Each successful exchange (`SuccA`, `SuccB`) includes the per-exchange
progress alternatives of the last two sentences. The assumptions of p.41 on `G` are
`BridgeCoverAssumptions`; the assumptions on the cover are the hypotheses on `S`. Primitivity refers
to the initial cover `S₀`, an input (the invariant of p.35). -/
theorem theorem_8_22 :
    (∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS lM : List (ℕ × ℕ)), BridgeCoverAssumptions I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonA I.graph (toEdges I.n lS) (toEdges I.n lM) →
        let S' := toEdges I.n ((alg (I, [l₀, lS, lM])).getD 0 [])
        let M' := toEdges I.n ((alg (I, [l₀, lS, lM])).getD 1 [])
        Relation.ReflTransGen (SuccA I.graph (toEdges I.n l₀))
            (toEdges I.n lS, toEdges I.n lM) (S', M') ∧
          br S' = 0 ∧ IsCanonA I.graph S' M' ∧
          costA S' M' ≤ costA (toEdges I.n lS) (toEdges I.n lM) ∧
          (0 < br (toEdges I.n lS) → LexA (toEdges I.n lS) S')) ∧
    (∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS : List (ℕ × ℕ)), BridgeCoverAssumptions I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonB I.graph (toEdges I.n lS) → BReady I.graph (toEdges I.n lS) →
        let S' := toEdges I.n ((alg (I, [l₀, lS])).getD 0 [])
        Relation.ReflTransGen (SuccB I.graph (toEdges I.n l₀)) (toEdges I.n lS) S' ∧
          br S' = 0 ∧ IsCanonB I.graph S' ∧ BReady I.graph S' ∧
          costB S' ≤ costB (toEdges I.n lS) ∧
          (0 < br (toEdges I.n lS) → LexB (toEdges I.n lS) S')) := by sorry

end TwoConnSS
