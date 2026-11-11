-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_3_1
-- name    : StochMatchQuery.Union.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:30.309539+00:00
-- url     : https://prove2.me/theorems/cf41166f-b142-4fc7-9251-9bf9bdbd910a
-- title:
--   Lemma 3.1 — Edge-marginal preservation
-- statement:
--   Let $(F,B)$ have any known joint law on subgraphs of a fixed finite simple graph, where $B\subseteq F$ is a matching and $\Delta(F)\le D$ on its support, with integer $D\ge1$. Edges of $F$ need not be independent. For every $h\in(0,1)$ there are independent vertex seeds and a measurable randomized matching map using $F$ and those seeds only, with
--   $$(1-h)\Pr(e\in B)\le\Pr(e\in\mathcal L(F))\le\Pr(e\in B),\qquad e\in E.$$
--   Its output is contained in $F$ and admits legal adaptive local computations of radius $R(D,h)$ with exactly (3.2). Fixed graph and law tables are freely available; seeds may only be used at vertices reached through present inspected edges. This is edgewise preservation with genuine locality.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: finite adaptive local computation with vertex randomness → well-founded decision trees with arbitrary measurable vertex seed spaces and legal sequential inspections; reason: each branch terminates; the next read depends only on earlier answers; present inspected paths determine reachability
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 3.1, PDF/printed p.11–12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 3 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_3_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (μ : Measure (Realization G × Realization G)) [IsProbabilityMeasure μ]
    (D : ℕ) (hD : 1 ≤ D)
    (hvalid : ∀ z, 0 < prob μ (fun a => a = z) →
      z.2 ⊆ z.1 ∧ IsMatching G z.2 ∧ maxDegree G z.1 ≤ D)
    (h : ℝ) (hh : 0 < h ∧ h < 1) :
    ∃ (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G),
      LocalMatching G (localRadius D h) ν alg ∧
      ∀ e, (1-h) * prob μ (fun z => e ∈ z.2) ≤
        prob ((Measure.map Prod.fst μ).prod ν.joint) (fun z => e ∈ alg z.1 z.2) ∧
        prob ((Measure.map Prod.fst μ).prod ν.joint) (fun z => e ∈ alg z.1 z.2) ≤
          prob μ (fun z => e ∈ z.2) := by sorry

end
end StochMatchQuery.Union
