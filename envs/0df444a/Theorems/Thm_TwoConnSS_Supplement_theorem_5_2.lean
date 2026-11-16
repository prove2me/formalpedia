-- Prove2me | Theorems.Thm_TwoConnSS_Supplement_theorem_5_2
-- name    : TwoConnSS.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:46:13.638103+00:00
-- url     : https://prove2.me/theorems/341542fc-e97c-46ec-a650-25a94f59d708
-- title:
--   Theorem 5.2 — a polynomial-time $(13/10+\varepsilon)$-approximation for 2VCSS
-- statement:
--   Let $G$ range over finite simple 2-vertex-connected graphs, and write $\mathrm{opt}_V(G)$ for the minimum number of edges of a 2-vertex-connected spanning subgraph of $G$.
--
--   For every fixed $\varepsilon>0$ there is a polynomial-time algorithm that, on every 2-vertex-connected input graph $G$, returns an edge set $F\subseteq E(G)$ such that $(V(G),F)$ is 2-vertex-connected and
--   $$
--   |F|\le\Bigl(\frac{13}{10}+\varepsilon\Bigr)\,\mathrm{opt}_V(G).
--   $$
--
--   This is the paper's vertex-connectivity result (Theorem 1.2 in the short version); it improves the previous ratios for 2VCSS.
--
--   **Formalization Note** One Turing machine (`Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`) per fixed $\varepsilon$, chosen before the instance. $\mathrm{opt}_V(G)$ is written as "for every 2VCSS $F'$ of $G$". Feasibility is `TwoConnSS.Supplement.IsTwoVCSS`.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm, no machine model named → `Turing.TM2ComputableInPolyTime` on the published encodings `encIn`/`encOut`, one machine per fixed $\varepsilon$; reason: Lean convention shared with the base mission's Theorem 5.1; same claim.
--   - encoding: $|F|\le(13/10+\varepsilon)\,\mathrm{opt}_V(G)$ → $|F|\le(13/10+\varepsilon)|F'|$ for every 2VCSS $F'$ of $G$; reason: the optimum is attained by some 2VCSS, so the two are equivalent; avoids an infimum.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), Theorem 5.2, p.19 (PDF 20); restates Theorem 1.2, p.2; proof §9.9, p.98 (PDF 99)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Supplement_IsTwoVCSS

namespace TwoConnSS.Supplement

open TwoConnSS

/-- **Theorem 5.2 (= Theorem 1.2): a polynomial-time (13/10 + ε)-approximation for 2VCSS.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 5.2, p.19 (restating
Theorem 1.2, p.2); proof §9.9, p.98: "For every fixed ε > 0 there is a polynomial-time
(13/10 + ε)-approximation algorithm for 2VCSS."

For every real `ε > 0` there is a function `alg`, computed by a polynomial-time Turing machine,
such that on every instance whose graph `G` is 2-vertex-connected the output `F` is a 2VCSS of `G`
and `|F| ≤ (13/10 + ε)·|F'|` for every 2VCSS `F'` of `G`.

**Formalization Note.** The machine is Mathlib's `Turing.TM2ComputableInPolyTime` on the published
encodings `encIn` (`n` in unary, then the adjacency matrix) and `encOut`; one machine per fixed
`ε`, chosen before the instance. OPT is "every feasible `F'`", never an infimum. Every simple graph
on `Fin n` that is 2VC (so `n ≥ 3`) is an input. -/
theorem theorem_5_2 :
    ∀ ε : ℝ, 0 < ε → ∃ alg : Inst → List (ℕ × ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, IsTwoVC I.graph →
        IsTwoVCSS I.graph (toEdges I.n (alg I)) ∧
        ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoVCSS I.graph F' →
          ((toEdges I.n (alg I)).card : ℝ) ≤ (13 / 10 + ε) * (F'.card : ℝ) := by sorry

end TwoConnSS.Supplement
