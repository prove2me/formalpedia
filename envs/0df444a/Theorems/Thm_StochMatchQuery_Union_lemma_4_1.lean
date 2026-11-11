-- Prove2me | Theorems.Thm_StochMatchQuery_Union_lemma_4_1
-- name    : StochMatchQuery.Union.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:12:18.540861+00:00
-- url     : https://prove2.me/theorems/cd2dd4b0-7ce9-4b6a-bfec-f3a07b0df23a
-- title:
--   Lemma 4.1 — Covariance for local computations
-- statement:
--   Let edges of a finite simple graph be independent with probabilities $\theta_e\in[0,1]$ and $\sum_{e\ni v}\theta_e\le\Lambda$. Give vertices arbitrary mutually independent measurable seeds, independent of the edges. Suppose $Y_v\in[0,1]$ is computed by a finite adaptive tree of radius $R$ under the reading rules of Lemma 4.1. For an independent copy $F'$ of $F$,
--   $$|\operatorname{Cov}(Y_u,Y_v)|\le\Pr(\operatorname{dist}_{F\cup F'}(u,v)\le2R+1),\qquad\sum_v|\operatorname{Cov}(Y_u,Y_v)|\le\sum_{j=0}^{2R+1}(2\Lambda)^j.$$
--   The second bound holds for every $u$ and includes the diagonal. Disconnected pairs are excluded by the bounded-walk event.
--
--   Differences from the source:
--   - encoding: finite adaptive local computation with vertex randomness → well-founded decision trees with arbitrary measurable vertex seed spaces and legal sequential inspections; reason: each branch terminates; the next read depends only on earlier answers; present inspected paths determine reachability
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 4.1, PDF/printed p.21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Round
import Definitions.Def_StochMatchQuery_Union_Thresholds

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical

/-- lemma 4 1; pinned source and all standing assumptions are recorded in items.yaml. -/
theorem lemma_4_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (theta : Edge G → ℝ) (htheta : ∀ e, 0 ≤ theta e ∧ theta e ≤ 1)
    (Lambda : ℝ) (hLambda : ∀ v, ∑ e ∈ incident G Finset.univ v, theta e ≤ Lambda)
    (ν : VertexLaw V) (R : ℕ)
    (Y : Realization G → ((v : V) → ν.carrier v) → V → ℝ)
    (hy : ∀ F ξ v, 0 ≤ Y F ξ v ∧ Y F ξ v ≤ 1)
    (hloc : ComputesLocally G R Y) :
    let μ := (realizationLaw G theta).prod ν.joint
    (∀ u v, |cov μ (fun z => Y z.1 z.2 u) (fun z => Y z.1 z.2 v)| ≤
      prob ((realizationLaw G theta).prod (realizationLaw G theta))
        (fun z => Reached G (z.1 ∪ z.2) u v (2*R+1))) ∧
    (∀ u, ∑ v : V, |cov μ (fun z => Y z.1 z.2 u) (fun z => Y z.1 z.2 v)| ≤
      ∑ j ∈ Finset.range (2*R+2), (2*Lambda)^j) := by sorry

end
end StochMatchQuery.Union
