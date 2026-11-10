-- Prove2me | Theorems.Thm_TwoConnSS_theorem_8_29
-- name    : TwoConnSS.theorem_8_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:50:30.261899+00:00
-- url     : https://prove2.me/theorems/fb6b6f33-c934-4175-bb65-49a449202d40
-- title:
--   Theorem 8.29 — exact completion: bounds (22)–(24) and $R\le m_{\ne4}$
-- statement:
--   Fix $0 < \varepsilon < 1/26$, $q = \lceil 1/\varepsilon\rceil$, and the structured-graph parameters. There is a polynomial-time algorithm (Algorithm A with its exact completion) that, on a structured graph $G$ with initial cover $S_0$, returns $(S, M)$ and $F_A$ such that $(S, M)$ is reached by Algorithm A and is at its contraction stage, $F_A$ is a 2ECSS of $G$, and
--
--   $$|F_A| = \mathrm{opt}_E(G') + L, \qquad \mathrm{opt}_E(G') \le \mathrm{opt}_E(G),$$
--   $$|F_A| \le \mathrm{cost}_A(S) + \frac{R}{117} - 2 \le K_A + \frac{R}{117} - 2, \tag{22}$$
--   $$R \le m_{\ne 4},\qquad |F_A| \le \tfrac54 m_4 + \tfrac{16}{13} m_{\ne 4} - 2, \tag{23}$$
--   $$|F_A| \le K_A + \frac{\mathrm{opt}_E(G)}{144}. \tag{24}$$
--
--   Here $G'$ contracts the large components, $L$ is their edge count and $R$ the edge count of the remaining 5–8-cycles. Bound (23) is Algorithm A's contribution to the final comparison.
--
--   Differences from the source:
--   - reading: S is the cover obtained by Algorithm A on G at its contraction stage, and the exact-completion algorithm returns F_A → there is a polynomial-time algorithm returning (S, M, F_A) with (S, M) reached from a Lemma 8.11 output by successful A-exchanges and at the contraction stage (`IsContractionStage`), and F_A satisfying every bound; reason: Algorithm A is defined only through its exchange lemmas; the reading 'for every reachable (S, M)' is not supported, since the proof of R ≤ m_{≠4} (Lemma B.2, p.102) uses how the specific exchanges absorb initial 4-cycles, not only that they are successful
--   - encoding: opt_E(G′) and opt_E(G) → a witness F° optimal among 2ECSS of G′ (`IsQTwoECSS`) with |F°| ≤ |F″| for every 2ECSS F″ of G, and (24) against every 2ECSS F″; reason: avoids infima; G′ is read in G with free moves inside contracted components, parallel edges kept
--   - encoding: the − 2 terms and R/117 → rational arithmetic; reason: no natural-number truncation
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 8.29, p.55 (PDF p.56); proof App. B.6, p.134

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_IsContractionStage
import Definitions.Def_TwoConnSS_IsQTwoECSS

namespace TwoConnSS

/-- **Theorem 8.29: exact completion (bounds (22)–(24)).**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 8.29, p.55 (proof in
App. B, p.134): "Let S be the bridgeless canonical weak 2-edge-cover obtained by Algorithm A on a
structured instance G, at its contraction stage. For fixed accuracy parameters, the exact-completion
algorithm returns in polynomial time a 2ECSS FA satisfying |FA| = optE(G′) + L, optE(G′) ≤ optE(G),
and |FA| ≤ costA(S) + R/117 − 2 ≤ KA + R/117 − 2. (22) Moreover, R ≤ m≠4, and the output satisfies
both |FA| ≤ (5/4)m4 + (16/13)·m≠4 − 2, (23) |FA| ≤ KA + optE(G)/144. (24)"

For `0 < ε < 1/26` (`q = ⌈1/ε⌉`), `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time
`alg` (Algorithm A with its exact completion) that, on a structured `G` with an initial cover `S₀`,
returns `[S, M, F_A]` such that:
1. `(S, M)` is reached by Algorithm A from `S₀` and is at its contraction stage
   (`IsContractionStage`);
2. `F_A` is a 2ECSS of `G`;
3. some optimal 2ECSS `F°` of the contracted multigraph `G'` (contract each large component of `S`)
   has `|F_A| = |F°| + L` and `|F°| ≤ |F''|` for every 2ECSS `F''` of `G` (`opt_E(G') ≤ opt_E(G)`);
4. `|F_A| ≤ cost_A(S) + R/117 − 2 ≤ K_A + R/117 − 2`;
5. `R ≤ m_{≠4}`;
6. `|F_A| ≤ (5/4)m₄ + (16/13)m_{≠4} − 2`;
7. `|F_A| ≤ K_A + |F''|/144` for every 2ECSS `F''` of `G`.

**Formalization Note.** "The cover obtained by Algorithm A at its contraction stage" is read as
the output of an algorithm whose run is pinned by `IsContractionStage` (Algorithm A's loop
conditions and successful exchanges); the theorem asserts that such an algorithm exists. The reading
"for every `(S, M)` reachable by successful A-exchanges" is not supported by the paper: its proof of
`R ≤ m_{≠4}` (Lemma B.2, p.102) uses how the specific exchanges of Algorithm A absorb initial
4-cycles, which the definition of a successful exchange does not record. All "− 2" bounds are in `ℚ`. `opt_E(G')` and `opt_E(G)` are
"every feasible solution" comparisons with a witness. -/
theorem theorem_8_29 (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1 / 26) (α η : ℝ) (hα₁ : 11 / 9 ≤ α)
    (hα₂ : α < 5 / 4) (hη₁ : 0 < η) (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) →
        let S₀ := toEdges I.n l₀
        let S := toEdges I.n ((alg (I, [l₀])).getD 0 [])
        let M := toEdges I.n ((alg (I, [l₀])).getD 1 [])
        let FA := toEdges I.n ((alg (I, [l₀])).getD 2 [])
        IsContractionStage I.graph ⌈1 / ε⌉₊ S₀ S M ∧
        IsTwoECSS I.graph FA ∧
        (∃ Fo, IsQTwoECSS I.graph (largeComps S) Fo ∧
          (∀ F', IsQTwoECSS I.graph (largeComps S) F' → Fo.card ≤ F'.card) ∧
          FA.card = Fo.card + Lsum S ∧
          ∀ F'', IsTwoECSS I.graph F'' → Fo.card ≤ F''.card) ∧
        (FA.card : ℚ) ≤ costA S M + (Rsum S : ℚ) / 117 - 2 ∧
        costA S M + (Rsum S : ℚ) / 117 - 2 ≤ KA S₀ + (Rsum S : ℚ) / 117 - 2 ∧
        Rsum S ≤ mNe4 S₀ ∧
        (FA.card : ℚ) ≤ 5 / 4 * (m4 S₀ : ℚ) + 16 / 13 * (mNe4 S₀ : ℚ) - 2 ∧
        ∀ F'', IsTwoECSS I.graph F'' → (FA.card : ℚ) ≤ KA S₀ + (F''.card : ℚ) / 144 := by sorry

end TwoConnSS
