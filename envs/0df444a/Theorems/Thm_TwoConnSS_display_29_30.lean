-- Prove2me | Theorems.Thm_TwoConnSS_display_29_30
-- name    : TwoConnSS.display_29_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:38.014195+00:00
-- url     : https://prove2.me/theorems/f9d9a084-4200-48ef-86e4-01647c122310
-- title:
--   Displays (29)–(30) — the two Algorithm-B bounds against $m_4^{\mathrm{merged}}$, $m_4^{\mathrm{surv}}$, $m_{\ne4}$
-- statement:
--   Let $G$ be structured with initial cover $S_0$. There is a polynomial-time algorithm (Algorithm B) returning a final configuration $S$ with large component $H$ ($h = |V(H)|$, $s$ surviving 4-cycles), reached from $S_0$ by successful exchanges of Algorithm B, and two 2ECSS solutions $F_{B,1}$, $F_{B,2}$ of $G$ such that, with $m_4^{\mathrm{surv}} = 4s$ and $m_4^{\mathrm{merged}} = m_4 - 4s$,
--   $$|F_{B,1}| = |E(H)| + 5s \le \tfrac65 m_4^{\mathrm{merged}} + \tfrac54 m_4^{\mathrm{surv}} + \tfrac{67}{50} m_{\ne 4} - 2, \tag{29}$$
--   $$|F_{B,2}| \le 5s + h + \kappa - 2,\quad \mathrm{opt}_E(G) \ge 5s + \kappa - 1,\quad h \le m_4^{\mathrm{merged}} + m_{\ne4},$$
--   $$|F_{B,2}| \le \mathrm{opt}_E(G) + m_4^{\mathrm{merged}} + m_{\ne 4} - 1. \tag{30}$$
--
--   These are Algorithm B's contributions to the final comparison.
--
--   Differences from the source:
--   - reading: the sequential-shortcut and matroid solutions of Algorithm B and its final configuration → there is a polynomial-time algorithm returning a final configuration reached from S₀ by successful B-exchanges and two 2ECSS solutions satisfying the displays; reason: Algorithm B is defined only through its exchange lemmas; the large-component merges of p.67 are successful B-exchanges
--   - encoding: m₄^merged, m₄^surv with m₄^merged + m₄^surv = m₄ → m₄^surv = 4s and m₄^merged = m₄ − 4s in ℚ; reason: the identity holds by definition; no truncation
--   - encoding: opt_E(G), the minimum size of a 2ECSS → a comparison with every 2ECSS `F'` of `G`; reason: avoids the junk value of an infimum; same instances
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4` on `encInL`/`encLists` (the graph, then the covers and pairings as edge lists), fixed before the instance; reason: Lean needs a machine model; covers and pairings are inputs and outputs of the procedure
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.4, displays (29)–(30), pp.71–72 (PDF pp.72–73)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover
import Definitions.Def_TwoConnSS_SuccB
import Definitions.Def_TwoConnSS_KA
import Definitions.Def_TwoConnSS_IsKappa

namespace TwoConnSS

/-- **Displays (29) and (30): the two Algorithm-B bounds.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.4, pp.71–72: "In Algorithm B,
let m4^merged count the edges of initial 4-cycle components absorbed before the last stage, and let
m4^surv = 4s count those in the s surviving components. … Let H be the final large component and put
h = |V(H)|. The sequential-shortcut solution FB,1 satisfies |FB,1| = |E(H)| + 5s ≤ (6/5)m4^merged +
(5/4)m4^surv + (67/50)·m≠4 − 2. (29) The matroid solution FB,2 and its lower bound give
|FB,2| ≤ 5s + h + κ − 2, optE(G) ≥ 5s + κ − 1. … h ≤ m4^merged + m≠4. Consequently,
|FB,2| ≤ optE(G) + m4^merged + m≠4 − 1. (30)"

For `11/9 ≤ α < 5/4`, `0 < η ≤ 1/100` there is a polynomial-time `alg` (Algorithm B) that, on a
structured `G` with an initial cover `S₀`, returns `[S, F_{B,1}, F_{B,2}]` such that, with `s` the
number of 4-cycle components of `S`, `m₄^surv = 4s` and `m₄^merged = m₄ − 4s`:
1. `S` is reached from `S₀` by a finite chain of successful B-exchanges and is in the final
   configuration with large component `H` (`h = |V(H)|`);
2. `F_{B,1}` is a 2ECSS with `|F_{B,1}| = |E(H)| + 5s` and (29)
   `|F_{B,1}| ≤ (6/5)m₄^merged + (5/4)m₄^surv + (67/50)m_{≠4} − 2`;
3. `F_{B,2}` is a 2ECSS, and for some `κ` of the final configuration
   `|F_{B,2}| ≤ 5s + h + κ − 2` and `|F'| ≥ 5s + κ − 1` for every 2ECSS `F'`;
4. `h ≤ m₄^merged + m_{≠4}`, and (30) `|F_{B,2}| ≤ |F'| + m₄^merged + m_{≠4} − 1` for every 2ECSS
   `F'`.

**Formalization Note.** These displays describe the output of Algorithm B, which is defined only
through its exchange lemmas; the statement asserts that an algorithm with these outputs exists, its
run pinned by the chain of successful B-exchanges (the large-component merges of p.67 are
successful B-exchanges too). `m₄^merged` is computed as `m₄ − 4s` in `ℚ`, so
`m₄^merged + m₄^surv = m₄` holds by definition. All "− 1", "− 2" bounds are in `ℚ`. -/
theorem display_29_30 (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst × List (List (ℕ × ℕ)) → List (List (ℕ × ℕ)),
      Nonempty (Turing.TM2ComputableInPolyTime encInL encLists alg) ∧
      ∀ (I : Inst) (l₀ : List (ℕ × ℕ)), Structured α η I.graph →
        IsInitialCover I.graph (toEdges I.n l₀) →
        let S₀ := toEdges I.n l₀
        let S := toEdges I.n ((alg (I, [l₀])).getD 0 [])
        let FB1 := toEdges I.n ((alg (I, [l₀])).getD 1 [])
        let FB2 := toEdges I.n ((alg (I, [l₀])).getD 2 [])
        let s : ℚ := ((cyc4 S).card : ℚ)
        let msurv : ℚ := 4 * s
        let mmerged : ℚ := (m4 S₀ : ℚ) - 4 * s
        Relation.ReflTransGen (SuccB I.graph S₀) S₀ S ∧
        ∃ H : Finset (Fin I.n), IsFinalConfigB I.graph S H ∧
          IsTwoECSS I.graph FB1 ∧ (FB1.card : ℚ) = ((edgesIn S H).card : ℚ) + 5 * s ∧
          (FB1.card : ℚ) ≤ 6 / 5 * mmerged + 5 / 4 * msurv + 67 / 50 * (mNe4 S₀ : ℚ) - 2 ∧
          IsTwoECSS I.graph FB2 ∧
          (∃ κ : ℕ, IsKappa I.graph S H κ ∧
            (FB2.card : ℚ) ≤ 5 * s + (H.card : ℚ) + (κ : ℚ) - 2 ∧
            ∀ F', IsTwoECSS I.graph F' → 5 * s + (κ : ℚ) - 1 ≤ (F'.card : ℚ)) ∧
          (H.card : ℚ) ≤ mmerged + (mNe4 S₀ : ℚ) ∧
          ∀ F', IsTwoECSS I.graph F' →
            (FB2.card : ℚ) ≤ (F'.card : ℚ) + mmerged + (mNe4 S₀ : ℚ) - 1 := by sorry

end TwoConnSS
