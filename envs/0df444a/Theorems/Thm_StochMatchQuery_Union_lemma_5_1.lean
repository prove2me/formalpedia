-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_5_1
-- name    : StochMatchQuery.Union.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:11:02.863176+00:00
-- url     : https://prove2.me/theorems/32d7250e-7c43-4995-b354-52bbaabc8504
-- title:
--   Lemma 5.1 — Trimming to bounded degree
-- statement:
--   Let a finite simple graph have nonnegative weights, a fractional matching $y$, $s\in(0,1]$, and $h\in(0,1)$. Let $F$ have independent edge probabilities $0\le\theta_e\le\min\{1,y_e/s\}$, and let $B\subseteq F$ be an arbitrary correlated reference matching with $\Pr(e\in B)\le y_e$. There are independent vertex seeds and a measurable local matching map $M=\mathcal L_{s,h}(F)\subseteq F$ such that
--   $$\Pr(e\in M)\le y_e,\quad\mathbb E[w(M)]\ge\mathbb E[w(B)]-2h\sum_ew_ey_e,\quad\sum_v|\operatorname{Cov}(1_{\{u\notin V(M)\}},1_{\{v\notin V(M)\}})|\le K_{\rm cov}(s,h).$$
--   The last inequality holds for every $u$. Its local radius is $R_{\rm raw}(s,h)$ with the exact definitions (5.4)–(5.6). The reference is used only through its law.
--
--   Differences from the source:
--   - encoding: joint laws of finite graph-valued random variables → finite laws on edge subsets, with pointwise requirements on their positive-mass support; reason: all source outcomes of a finite random object are represented; null atoms impose no restrictions on a law
--   - encoding: finite adaptive local computation with vertex randomness → well-founded decision trees with arbitrary measurable vertex seed spaces and legal sequential inspections; reason: each branch terminates; the next read depends only on earlier answers; present inspected paths determine reachability
--   - generalization: the algorithm uses F and fresh independent randomness assigned to vertices → additionally, the output is a legal local computation (LocalMatching) of radius R_raw(s,h) in F; reason: proved in Step 4 of the source proof and used in §7 through Lemma 4.1; dropping the extra clause gives the printed statement
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 5.1, PDF/printed p.23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 5 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_5_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w y theta : Edge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hy : InFM G y) (s h : ℝ) (hs : 0 < s ∧ s ≤ 1) (hh : 0 < h ∧ h < 1)
    (htheta : ∀ e, 0 ≤ theta e ∧ theta e ≤ 1 ∧ theta e ≤ y e/s)
    (μ : Measure (Realization G × Realization G)) [IsProbabilityMeasure μ]
    (hlaw : Measure.map Prod.fst μ = realizationLaw G theta)
    (hB : ∀ z, 0 < prob μ (fun a => a = z) → z.2 ⊆ z.1 ∧ IsMatching G z.2)
    (hmarg : ∀ e, prob μ (fun z => e ∈ z.2) ≤ y e) :
    ∃ (ν : VertexLaw V) (alg : Realization G → ((v : V) → ν.carrier v) → Realization G),
      LocalMatching G (rawRadius s h) ν alg ∧
      let law := (realizationLaw G theta).prod ν.joint
      (∀ e, prob law (fun z => e ∈ alg z.1 z.2) ≤ y e) ∧
      mean law (fun z => weightOf w (alg z.1 z.2)) ≥
        mean μ (fun z => weightOf w z.2) - 2*h*(∑ e, w e*y e) ∧
      (∀ u, ∑ v : V, |cov law (fun z => ind (u ∉ vertices G (alg z.1 z.2)))
        (fun z => ind (v ∉ vertices G (alg z.1 z.2)))| ≤ covarianceBound s h) := by sorry

end
end StochMatchQuery.Union
