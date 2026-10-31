-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_xopt_mem_FM
-- name    : ProphetMatchingEFGT.xopt_mem_FM
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:32.58722+00:00
-- url     : https://prove2.me/theorems/98c1212c-8764-4cd9-af92-290792c5120e
-- title:
--   §3 — the marginals $x^{opt}_e=\Pr[e\in\mathrm{OPT}(w)]$ lie in $\mathcal F_M$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with independent edge weights $w_e\sim F_e$, and let $\mathrm{OPT}(w)$ be a deterministic maximum-weight matching with measurable level sets. Let
--   $$x^{opt}_e=\Pr_{w}\big[e\in\mathrm{OPT}(w)\big]\qquad(e\in E).$$
--   Then $x^{opt}\in\mathcal F_M$.
--
--   Together with Theorem 2.3, this reduces the matching prophet inequality to constructing OCRSs for every point of $\mathcal F_M$.
--
--   Differences from the source:
--   - reading: x^opt_uv defined as Pr[(uv) ∈ R(w, F)], then identified with Pr[(uv) ∈ OPT(w)] → x^opt_e := Pr[e ∈ OPT(w)]; reason: the same sentence states the identification; the milestone is the conclusion x^opt ∈ FM
--   - encoding: OPT a deterministic function returning a maximum-weight feasible set (p.8, footnote 5) → any opt with opt w ∈ M, maximal weight, and measurable level sets {w | opt w = S}; reason: measurability is needed for Pr[OPT(w) = S] to be defined; the theorem holds for every such OPT
--   - reading: a graph G = (V, E) (not necessarily bipartite) whose edges are written (uv) (§3, p.9) → a Mathlib SimpleGraph on a finite vertex type: no loops, at most one edge between two vertices; reason: the notation (uv), x_uv and FM's Σ_u y(uv) (p.10) presume one edge per pair of vertices, and (11), (13) use that (uv) is the only u–v edge
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §3, p. 10

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_BatchedModel
import Definitions.Def_ProphetMatchingEFGT_MatchingModel

open MeasureTheory

namespace ProphetMatchingEFGT

/-- **§3, p. 10: `x^opt ∈ FM`.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, §3, p. 10: "Note that for any edge `(uv)`, `x^opt_uv`
is precisely the probability that the edge `(uv)` is in `OPT(w)`, where `w ∼ F`. Therefore,
`x^opt ∈ FM`."

**Formalization Note.** `x^opt_e = Pr_{w ∼ ∏ F_e}[e ∈ OPT(w)]`, for any deterministic maximum-weight
matching `OPT` with measurable level sets. The edge weights are independent (`Measure.pi F`). -/
theorem xopt_mem_FM {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (F : Edge G → Measure ℝ) [∀ e, IsProbabilityMeasure (F e)]
    (opt : (Edge G → ℝ) → Finset (Edge G)) (hopt : IsOPT (matchingFamily G) opt) :
    InFM G (fun e => (Measure.pi F).real {w | e ∈ opt w}) := by sorry

end ProphetMatchingEFGT
