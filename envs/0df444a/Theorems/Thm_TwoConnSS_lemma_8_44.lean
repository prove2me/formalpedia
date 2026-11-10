-- Prove2me | Theorems.Thm_TwoConnSS_lemma_8_44
-- name    : TwoConnSS.lemma_8_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:59.419547+00:00
-- url     : https://prove2.me/theorems/d81b28d7-7f5d-40a8-a83e-dd07e1301e00
-- title:
--   Lemma 8.44 — a 2ECSS with at most $5s+h+\kappa-2$ edges
-- statement:
--   Let $G$ be structured and $S$ in the final configuration of Algorithm B, with large component $L$, $h = |V(L)|$, $s$ 4-cycle components and $\kappa$ as above. In polynomial time one can construct a 2ECSS $S^{(2)}$ of $G$ with
--   $$|S^{(2)}| \le 5s + h + \kappa - 2.$$
--
--   This is the matroid-intersection solution of Algorithm B.
--
--   Differences from the source:
--   - reading: the final configuration of §8.3.4 → `IsFinalConfigB` with G structured; reason: the properties §8.3.4 states
--   - encoding: κ and the − 2 term → any κ with `IsKappa`; the bound in ℤ; reason: a minimum with a witness; no truncation
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Lemma 8.44, p.70 (PDF p.71)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsKappa

namespace TwoConnSS

/-- **Lemma 8.44: the matroid solution of Algorithm B.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Lemma 8.44, p.70: "In polynomial
time, one can construct a 2-ECSS solution S(2) satisfying |S(2)| ≤ 5s + h + κ − 2."

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` such that for every
structured `G` and every `S` in the final configuration of Algorithm B with large component `L`
(`h = |V(L)|`, `s` the number of 4-cycle components, `κ` as on p.68), the output `S^{(2)}` is a 2ECSS
of `G` with `|S^{(2)}| ≤ 5s + h + κ − 2`.

**Formalization Note.** The input is `(G, [S])`. The bound is in `ℤ`. -/
theorem lemma_8_44 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (lS : List (ℕ × ℕ)) (L : Finset (Fin I.n)) (κ : ℕ), Structured α η I.graph →
        IsFinalConfigB I.graph (toEdges I.n lS) L → IsKappa I.graph (toEdges I.n lS) L κ →
        let S2 := toEdges I.n ((alg (I, [lS])).getD 0 [])
        IsTwoECSS I.graph S2 ∧
        (S2.card : ℤ) ≤ 5 * ((cyc4 (toEdges I.n lS)).card : ℤ) + (L.card : ℤ) + (κ : ℤ) - 2 := by sorry

end TwoConnSS
