-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_Supplement_graph_encoding
-- name    : StabPauli1264.Grouped.Supplement.graph_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:52:09.804554+00:00
-- url     : https://prove2.me/theorems/df944bf0-51ef-43fe-98cd-398ad6e542a4
-- title:
--   Lemma 3.1 — Graph encoding
-- statement:
--   Let $H$ be a graph on $[m]$, $m\ge1$, and let $M_H$ be the $m$-qubit window with $P_v=X_v\prod_{u<v,\,uv\in E(H)}Z_u$. Then:
--
--   1. the frustration graph of $M_H$ is $H$, and the labels of $M_H$ are linearly independent;
--   2. for every $c\in[0,\infty)^m$, $h_{M_H}(c)=\alpha_c(H)$;
--   3. for every inclusion-maximal independent set $T$ of $H$, every pure stabilizer state $\sigma$ with $P_v\sigma=\sigma$ for all $v\in T$ has response $f_\sigma=\mathbf 1_T$.
--
--   Thus proper ERM on $M_H$ solves maximum-weight independent set on $H$, and every graph is a frustration graph.
--
--   Differences from the source:
--   - encoding: vertices and qubits [m], order u < v → Fin m with its order; reason: relabelling only
--   - encoding: a pure stabilizer state stabilized by P_v → the projector σ_T of a valid tableau with P_v σ_T = σ_T; reason: definition of being stabilized
--   - encoding: a graph with m vertices → m ≥ 1; reason: windows are nonempty (standing assumption, Definition 1.1)
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 3.1, p. 10; Eq. (9) p. 10; proof p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-- Lemma 3.1 (Graph encoding), p. 10: `M_H` has frustration graph `H` and independent labels;
`h_{M_H}(c) = α_c(H)` for `c ≥ 0`; every pure stabilizer state stabilized by `P_v, v ∈ T`, for an
inclusion-maximal independent set `T`, has response `1_T`. -/
theorem graph_encoding {m : ℕ} (H : SimpleGraph (Fin m)) (hm : 0 < m) :
    frustrationGraph (graphWindow H hm) = H ∧
    IndepLabels (graphWindow H hm) Finset.univ ∧
    (∀ c : Fin m → ℝ, (∀ v, 0 ≤ c v) → supportFn (graphWindow H hm) c = indepWeight H c) ∧
    ∀ T : Finset (Fin m), IsMaximalIndep H T → ∀ S : Tableau m, IsValidTableau S →
      (∀ v ∈ T, operator (graphWindow H hm) v * tableauProjector S = tableauProjector S) →
      response (graphWindow H hm) S = fun v => if v ∈ T then 1 else 0 := by sorry

end StabPauli1264.Grouped.Supplement
