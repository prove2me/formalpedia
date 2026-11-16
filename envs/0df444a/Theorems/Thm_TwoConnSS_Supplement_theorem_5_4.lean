-- Prove2me | Theorems.Thm_TwoConnSS_Supplement_theorem_5_4
-- name    : TwoConnSS.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:47:29.501643+00:00
-- url     : https://prove2.me/theorems/eecfe897-e4dc-4220-9b2f-9fcd87d990ae
-- title:
--   Theorem 5.4 — 2VCSS within $(9/7)\mu+\varepsilon$ from a $\mu$-approximation for $\{3,4\}$-cycle-free 2-edge-covers
-- statement:
--   Write $\mathrm{opt}_V(G)$ for the minimum number of edges of a 2-vertex-connected spanning subgraph of a 2-vertex-connected graph $G$. Suppose that, for a real $\mu\ge1$, there is a polynomial-time $\mu$-approximation algorithm for minimum $\{3,4\}$-cycle-free 2-edge-cover in 2-edge-connected graphs (the hypothesis $\mathrm{CoverApprox}(\mu)$).
--
--   Then for every fixed $\varepsilon>0$ there is a polynomial-time algorithm that, on every 2-vertex-connected graph $G$, returns an edge set $F\subseteq E(G)$ with $(V(G),F)$ 2-vertex-connected and
--   $$
--   |F|\le\Bigl(\frac{9}{7}\mu+\varepsilon\Bigr)\mathrm{opt}_V(G).
--   $$
--
--   With an exact cover algorithm ($\mu=1$) this would give a $(9/7+\varepsilon)$-approximation for 2VCSS.
--
--   **Formalization Note** Machines are `Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`, one per fixed $\varepsilon$. The cover algorithm is assumed on 2EC graphs (not only 2VC ones), as in the source: the proof applies it to five-edge subdivision instances, which are 2EC but not 2VC.
--
--   Differences from the source:
--   - reading: a $\mu$-approximation for the cover problem "in 2-edge-connected graphs" → required only on 2EC graphs that admit a $\{3,4\}$-cycle-free 2-edge-cover; reason: the triangle and the 4-cycle are 2EC with no such cover, so the literal reading makes the hypothesis unsatisfiable; this is the weaker hypothesis, hence the stronger theorem.
--   - encoding: polynomial-time algorithm, no machine model named → `Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`; reason: Lean convention shared with the base Theorem 5.1.
--   - encoding: $\mathrm{opt}_V(G)$ → every 2VCSS $F'$ of $G$; reason: the optimum is attained; equivalent.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), Theorem 5.4, p.20 (PDF 21); restates Theorem 1.4, p.3; proof §9.9, p.98 (PDF 99)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Supplement_IsTwoVCSS
import Definitions.Def_TwoConnSS_Supplement_CoverApprox

namespace TwoConnSS.Supplement

open TwoConnSS

/-- **Theorem 5.4 (= Theorem 1.4): 2VCSS from an approximation for {3, 4}-cycle-free
2-edge-covers.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 5.4, p.20 (restating
Theorem 1.4, p.3); proof §9.9, p.98: "Suppose there is a polynomial-time μ-approximation algorithm
for minimum {3, 4}-cycle-free 2-edge-cover in 2-edge-connected graphs, where μ ≥ 1. Then, for every
fixed ε > 0, there is a polynomial-time (9/7 μ + ε)-approximation algorithm for 2VCSS."

If `μ ≥ 1` and `CoverApprox μ` holds, then for every real `ε > 0` there is a polynomial-time `alg`
that on every 2VC instance `G` outputs a 2VCSS `F` with `|F| ≤ ((9/7)·μ + ε)·|F'|` for every 2VCSS
`F'` of `G`.

**Formalization Note.** The cover algorithm of `CoverApprox` is required on every 2EC graph that
has a {3, 4}-cycle-free 2-edge-cover, not only on 2VC graphs: the proof (p.98) applies it to
five-edge subdivision instances, which are 2EC but not 2VC. Machines are
`Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`, one per fixed `ε`. OPT is "every feasible
`F'`". -/
theorem theorem_5_4 :
    ∀ μ : ℝ, 1 ≤ μ → CoverApprox μ →
      ∀ ε : ℝ, 0 < ε → ∃ alg : Inst → List (ℕ × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
        ∀ I : Inst, IsTwoVC I.graph →
          IsTwoVCSS I.graph (toEdges I.n (alg I)) ∧
          ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoVCSS I.graph F' →
            ((toEdges I.n (alg I)).card : ℝ) ≤ (9 / 7 * μ + ε) * (F'.card : ℝ) := by sorry

end TwoConnSS.Supplement
