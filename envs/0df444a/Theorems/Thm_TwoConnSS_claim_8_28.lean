-- Prove2me | Theorems.Thm_TwoConnSS_claim_8_28
-- name    : TwoConnSS.claim_8_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:49:19.352371+00:00
-- url     : https://prove2.me/theorems/b6d6cabe-3303-4bbb-abc6-d18007d96ba5
-- title:
--   Claim 8.28 — long component cycles, or an optimal 2ECSS
-- statement:
--   Fix $0 < \varepsilon < 1/26$ and put $q = \lceil 1/\varepsilon \rceil$. Let $G$ be structured with initial cover $S_0$, and let $(S, M)$ be a bridgeless canonical weak 2-edge-cover for Algorithm A (4-cycle components primitive) in which every part of $Q(S, M)$ has fewer than $q$ vertices. In polynomial time one can either
--
--   1. compute an optimal 2ECSS of $G$, or
--   2. find a successful exchange of Algorithm A to $(S', M')$ with $S'$ bridgeless, fewer connected components than $S$, every old block preserved, and $W_A(S') > W_A(S)$.
--
--   The claim yields a huge component (at least $26$ vertices) for Algorithm A, or solves the instance exactly when the auxiliary graph has bounded treewidth.
--
--   Differences from the source:
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - reading: the initial cover S₀ and the primitive-4-cycle invariant (p.35: 'Our exchanges maintain that every 4-cycle component is primitive') → an input `S₀` with `IsInitialCover G S₀`, and every 4-cycle component of `S` primitive relative to `S₀`; reason: primitivity and the successful exchanges are defined relative to S₀, so it must be an argument
--   - encoding: opt_E(G), the minimum size of a 2ECSS → a comparison with every 2ECSS `F'` of `G`; reason: avoids the junk value of an infimum; same instances
--   - encoding: polynomial time, for fixed ε → one TM2 machine per ε (and α, η), on `encInL`/`encLists`, whose output [F, M'] satisfies one of the two alternatives; reason: Lean needs a machine model; the output is read as the solution or the exchanged cover
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Claim 8.28, p.53 (PDF p.54)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccA
import Definitions.Def_TwoConnSS_partGraph

namespace TwoConnSS

/-- **Claim 8.28: long component cycles, or an optimal 2ECSS.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Claim 8.28, p.53: "Fix 0 < ε < 1/26
and put q = ⌈1/ε⌉. Let S be a bridgeless canonical weak 2-edge-cover for Algorithm A, and suppose
that every part of Q(S, M) has fewer than q vertices. In polynomial time, one can either compute an
optimal 2ECSS or find a successful exchange under assignment A whose output is bridgeless and has
fewer connected components. In the exchange alternative, every old block vertex set is preserved and
WA(S′) > WA(S)."

For `0 < ε < 1/26`, `q = ⌈1/ε⌉`, `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100`, there is a polynomial-time
`alg` such that for every structured `G`, initial cover `S₀`, and `(S, M)` canonical for A with `S`
bridgeless, every 4-cycle component of `S` primitive and every part of `Q(S, M)` on fewer than `q`
vertices, the output `[F, M']` satisfies one of:
1. `F` is a 2ECSS of `G` with `|F| ≤ |F'|` for every 2ECSS `F'`;
2. `(S, M) → (F, M')` is a successful A-exchange (so every old block lies in a new block), `F` is
   bridgeless, `F` has fewer connected components than `S`, and `W_A(F) > W_A(S)`.

**Formalization Note.** One machine per `ε` (and `α, η`), fixed before the instance. Connected
components count isolated vertices (p.33: "comp(S) always counts actual connected components").
`G` structured is the standing assumption of §8. The proof cites Birmelé [1] and an exact
bounded-treewidth algorithm ([23]). -/
theorem claim_8_28 (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1 / 26) (α η : ℝ) (hα₁ : 11 / 9 ≤ α)
    (hα₂ : α < 5 / 4) (hη₁ : 0 < η) (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ lS lM : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) → Primitive (toEdges I.n l₀) (toEdges I.n lS) →
        IsCanonA I.graph (toEdges I.n lS) (toEdges I.n lM) → br (toEdges I.n lS) = 0 →
        (∀ P ∈ parts (toEdges I.n lS) (toEdges I.n lM), P.card < ⌈1 / ε⌉₊) →
        let F := toEdges I.n ((alg (I, [l₀, lS, lM])).getD 0 [])
        let M' := toEdges I.n ((alg (I, [l₀, lS, lM])).getD 1 [])
        (IsTwoECSS I.graph F ∧ ∀ F', IsTwoECSS I.graph F' → F.card ≤ F'.card) ∨
        (SuccA I.graph (toEdges I.n l₀) (toEdges I.n lS, toEdges I.n lM) (F, M') ∧
          br F = 0 ∧ (comps F).card < (comps (toEdges I.n lS)).card ∧
          WA (toEdges I.n lS) < WA F) := by sorry

end TwoConnSS
