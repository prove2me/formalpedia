-- Prove2me | Theorems.Thm_TwoConnSS_lemma_8_11
-- name    : TwoConnSS.lemma_8_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:37.738189+00:00
-- url     : https://prove2.me/theorems/976ce836-537f-44d2-bf9d-bf3cc3464a46
-- title:
--   Lemma 8.11 — a canonical weak 2-edge-cover with $\mathrm{cost}_A(S)\le \frac54 m_4+\frac{11}{9}m_{\ne4}$
-- statement:
--   Let $G$ be a structured graph and $S_0$ an initial cover of $G$. In polynomial time one can compute $S$ and a pairing $M$ such that $(S, M)$ is a canonical weak 2-edge-cover for Algorithm A and
--   $$\mathrm{cost}_A(S) \le \tfrac54 m_4 + \tfrac{11}{9} m_{\ne 4}.$$
--   Moreover $S \subseteq S_0$ and every 4-cycle component of $S$ is primitive.
--
--   This is the first step of Algorithm A: the initial budget of $1/4$ per 4-cycle edge and $2/9$ per other edge pays all assignment-A credits.
--
--   Differences from the source:
--   - generalization: the conclusion: (S, M) canonical for A with cost_A(S) ≤ (5/4)m₄ + (11/9)m_{≠4} → additionally S ⊆ S₀ and every 4-cycle component of S primitive; reason: the proof deletes only bridges ('Only bridges have been deleted, so all original blocks remain intact', p.37); dropping the extra conjuncts gives the source's statement
--   - reading: an initial canonical cover S₀ with the properties stated above → an input with `IsInitialCover G S₀`; reason: the properties stated in §8.1
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 8.11, p.36 (PDF p.37); proof, p.37

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_costA
import Definitions.Def_TwoConnSS_KA
import Definitions.Def_TwoConnSS_Primitive

namespace TwoConnSS

/-- **Lemma 8.11: the initial transformation for Algorithm A.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 8.11, p.36: "From an initial
canonical cover S0 with the properties stated above, one can obtain, in polynomial time, a spanning
subgraph S that, together with a pairing M, is a canonical weak 2-edge-cover for Algorithm A and
satisfies costA(S) ≤ (5/4)m4 + (11/9)·m≠4."

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` that, given a structured
graph `G` and an initial cover `S₀` of it, returns `(S, M)` with: `(S, M)` canonical for A;
`cost_A(S, M) ≤ K_A = (5/4)m₄ + (11/9)m_{≠4}`; `S ⊆ S₀`; every 4-cycle component of `S` primitive.

**Formalization Note.** The input is `(G, [S₀])` and the output `[S, M]`, as edge lists. The last
two clauses are what the proof gives (p.37: "Only bridges have been deleted, so all original blocks
remain intact"), used later by Theorem 8.29. -/
theorem lemma_8_11 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) →
        let S := toEdges I.n ((alg (I, [l₀])).getD 0 [])
        let M := toEdges I.n ((alg (I, [l₀])).getD 1 [])
        IsCanonA I.graph S M ∧ costA S M ≤ KA (toEdges I.n l₀) ∧ S ⊆ toEdges I.n l₀ ∧
          Primitive (toEdges I.n l₀) S := by sorry

end TwoConnSS
