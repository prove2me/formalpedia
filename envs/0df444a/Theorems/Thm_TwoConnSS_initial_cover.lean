-- Prove2me | Theorems.Thm_TwoConnSS_initial_cover
-- name    : TwoConnSS.initial_cover
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:10.384436+00:00
-- url     : https://prove2.me/theorems/d72fbbdc-e774-465e-a80a-1d1d2cc89b84
-- title:
--   §8.1 — the initial cover: minimum triangle-free, canonical, five-vertex blocks, a 32-vertex component, 4-cycles merged
-- statement:
--   Let $11/9 \le \alpha < 5/4$ and $0 < \eta \le 1/100$. There is a polynomial-time algorithm that, on every $(\alpha,\eta)$-structured graph $G$, returns an edge set $S_0$ such that:
--
--   1. $S_0$ is a triangle-free 2-edge-cover of $G$ of minimum size among triangle-free 2-edge-covers;
--   2. every 2EC component of $S_0$ with fewer than nine edges is a cycle;
--   3. every 2EC block of a complex component of $S_0$ has at least five vertices (Lemma 8.3);
--   4. some component of $S_0$ has at least $32$ vertices;
--   5. no two 4-cycle components of $S_0$ have a spanning 8-cycle of $G$ on their union.
--
--   This cover is canonical for both algorithms, and its edge counts $m_4$, $m_{\ne 4}$ drive the final comparison.
--
--   Differences from the source:
--   - reading: the cover produced by Lemma 6.4, the canonicalization of [20, Definition 3, Lemma 6, Appendix B] and the initial 4-cycle merging → an output satisfying `IsInitialCover`, the properties these pages state for that procedure's result; reason: the cited procedure is not defined in the paper; its stated output properties are what the analysis uses
--   - reading: G a structured instance (the standing assumption of Section 8, p.32) → a hypothesis `Structured α η G` for 11/9 ≤ α < 5/4, 0 < η ≤ 1/100; reason: Section 8 fixes these parameters and works on structured graphs throughout (p.32: 'We henceforth use 11/9 ≤ α < 5/4')
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4`, fixed before the instance, on the encodings `encIn`/`encOut` (n in unary, then the adjacency matrix; edge lists in binary); reason: Lean needs a machine model; the input length is at least n², so polynomial in the code length is polynomial in n
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1, pp.32–33 (PDF pp.33–34): "Initial cover and the five-vertex block property", Lemma 8.3, "Initial 4-cycle merging before assigning credits"

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Structured
import Definitions.Def_TwoConnSS_IsInitialCover

namespace TwoConnSS

/-- **§8.1, initial cover (with Lemma 8.3 and initial 4-cycle merging).**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1, pp.32–33: "We compute a
minimum triangle-free 2-edge-cover using Lemma 6.4 and apply the canonicalization in [20, Definition
3, Lemma 6, and Appendix B]. This construction gives a minimum triangle-free canonical cover S̃
containing a component with at least 32 vertices. … Every 2EC component with fewer than nine edges
is a cycle." Lemma 8.3: "In the cover produced by the local-search canonicalization of [20, Appendix
B], every block of a complex component has at least five vertices." "We exhaustively merge two
4-cycle components whenever their union admits a spanning 8-cycle in G, replacing their edges by
those of that cycle. This preserves the size of the cover and its other canonical properties …
this procedure runs in polynomial time."

For `11/9 ≤ α < 5/4` and `0 < η ≤ 1/100` there is a polynomial-time `alg` whose output on every
instance with an `(α, η)`-structured graph `G` is an initial cover `S₀` of `G` (`IsInitialCover`):
a minimum triangle-free 2-edge-cover, every 2EC component with fewer than nine edges a cycle, every
block of a complex component on at least five vertices, a component on at least 32 vertices, and no
two 4-cycle components spanned by an 8-cycle of `G`.

**Formalization Note.** The procedure of [20, Appendix B] is replaced by the properties of its
output stated on these pages (procedure-free reading). The machine is fixed after `α, η`, before the
instance. -/
theorem initial_cover (α η : ℝ) (hα₁ : 11 / 9 ≤ α) (hα₂ : α < 5 / 4) (hη₁ : 0 < η)
    (hη₂ : η ≤ 1 / 100) :
    ∃ alg : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, Structured α η I.graph → IsInitialCover I.graph (toEdges I.n (alg I)) := by sorry

end TwoConnSS
